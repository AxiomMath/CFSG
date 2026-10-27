module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.SquareLinear
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabPrimeSU
public import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusNodeRoots
public import CFSG.ClassicalInvolution.ModelFacts.OddCover.ThreeQ
import CFSG.LinearAlgebra.LinearGroups.UnitaryScalarKernel
import all CFSG.LieType.Universal.Unitary.Roots

public section

namespace CFSG.AGLEmbeddingD2.SquareUnitary

open CFSG.SectionRank CFSG.SectionRank.ClassicalEven CFSG.Assembly.LowTwoRank

local notation "A₅" => alternatingGroup (Fin 5)

section Generic

theorem two_pow_mod_three_of_even {f : ℕ} (hf : Even f) : 2 ^ f % 3 = 1 := by
  obtain ⟨k, rfl⟩ := hf
  rw [← two_mul, pow_mul, Nat.pow_mod]
  norm_num

theorem two_pow_mod_three_of_odd {f : ℕ} (hf : Odd f) : 2 ^ f % 3 = 2 := by
  obtain ⟨k, rfl⟩ := hf
  rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
  norm_num

variable {G : Type*} [Group G]

theorem isCyclic_of_le_of_equiv {r : ℕ} {L : Subgroup G} {M : Type*} [Group M] (e : ↥L ≃* M)
    (h : ∀ Q : Subgroup M, IsPGroup r Q → IsCyclic Q) {P : Subgroup G} (hPL : P ≤ L)
    (hP : IsPGroup r P) : IsCyclic P := by
  have h1 : IsPGroup r (P.subgroupOf L) := hP.comap_subtype
  have h2 : IsCyclic ((P.subgroupOf L).map e.toMonoidHom) := h _ (h1.map _)
  have h3 : IsCyclic (P.subgroupOf L) :=
    isCyclic_of_surjective ((P.subgroupOf L).equivMapOfInjective e.toMonoidHom e.injective).symm
      ((P.subgroupOf L).equivMapOfInjective e.toMonoidHom e.injective).symm.surjective
  exact (Subgroup.subgroupOfEquivOfLe hPL).isCyclic.mp h3

theorem eq_bot_of_le_of_equiv {r : ℕ} {L : Subgroup G} {M : Type*} [Group M] (e : ↥L ≃* M)
    (h : ∀ Q : Subgroup M, IsPGroup r Q → Q = ⊥) {P : Subgroup G} (hPL : P ≤ L)
    (hP : IsPGroup r P) : P = ⊥ := by
  have h1 : IsPGroup r (P.subgroupOf L) := hP.comap_subtype
  have h2 : (P.subgroupOf L).map e.toMonoidHom = ⊥ := h _ (h1.map _)
  have h3 : P.subgroupOf L = ⊥ := (Subgroup.map_eq_bot_iff_of_injective _ e.injective).1 h2
  exact (Subgroup.subgroupOf_eq_bot.1 h3).eq_bot_of_le hPL

theorem isCyclic_of_map {H : Type*} [Group H] (θ : G →* H) (P : Subgroup G)
    (hinj : ∀ x ∈ P, θ x = 1 → x = 1) (h : IsCyclic (P.map θ)) : IsCyclic P := by
  have hi : Function.Injective (θ.comp P.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    exact Subgroup.mem_bot.2 (Subtype.ext (hinj x x.2 hx))
  have hr : (θ.comp P.subtype).range = P.map θ := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  exact (MonoidHom.ofInjective hi).isCyclic.mpr (hr ▸ h)

theorem false_of_hasSubquotient_sup_of_commutes [Finite G] {A B : Subgroup G}
    (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    (hA : ∀ P : Subgroup G, P ≤ A → IsPGroup 5 P → IsCyclic P)
    (hB : ∀ P : Subgroup G, P ≤ B → IsPGroup 5 P → P = ⊥)
    (h : LeviSection.HasSubquotient (A ⊔ B) (A₅ × A₅)) : False := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  let φ : ↥A × ↥B →* G := MonoidHom.noncommCoprod A.subtype B.subtype
    (fun a b => hAB a a.2 b b.2)
  have hφ : (⊤ : Subgroup (↥A × ↥B)).map φ = A ⊔ B := by
    rw [← MonoidHom.range_eq_map]
    exact (MonoidHom.noncommCoprod_range A.subtype B.subtype _).trans
      (by rw [Subgroup.range_subtype, Subgroup.range_subtype])
  have h' : LeviSection.HasSubquotient (⊤ : Subgroup (↥A × ↥B)) (A₅ × A₅) :=
    LeviSection.HasSubquotient.of_map φ (hφ ▸ h)
  refine h'.false_of_isCyclic (fun P _ hP => ?_) LeviSection.exists_not_isCyclic_five
  have hPB : ∀ x ∈ P, x.2 = 1 := by
    have h1 : IsPGroup 5 (P.map (MonoidHom.snd ↥A ↥B)) := hP.map _
    have h2 : (P.map (MonoidHom.snd ↥A ↥B)).map B.subtype = ⊥ :=
      hB _ (by rintro _ ⟨_, ⟨x, -, rfl⟩, rfl⟩; exact x.2.2) (h1.map _)
    intro x hx
    have hmem : B.subtype (MonoidHom.snd ↥A ↥B x) ∈
        (P.map (MonoidHom.snd ↥A ↥B)).map B.subtype := ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    rw [h2, Subgroup.mem_bot] at hmem
    exact Subtype.ext hmem
  refine isCyclic_of_map (MonoidHom.fst ↥A ↥B) P (fun x hx h1 => Prod.ext h1 (hPB x hx)) ?_
  have h1 : IsPGroup 5 ((P.map (MonoidHom.fst ↥A ↥B)).map A.subtype) := (hP.map _).map _
  have h2 := hA _ (by rintro _ ⟨_, ⟨x, -, rfl⟩, rfl⟩; exact x.1.2) h1
  have e := (P.map (MonoidHom.fst ↥A ↥B)).equivMapOfInjective A.subtype A.subtype_injective
  exact isCyclic_of_surjective e.symm.toMonoidHom e.symm.surjective

section Rank

variable {K Y : Type*} [Group K] [Group Y]

theorem three_le_pRank_of_indep [Finite Y] {π : K →* Y} {J : Subgroup Y} {x y z : K}
    (hxy : Commute x y) (hxz : Commute x z) (hyz : Commute y z) (hx3 : x ^ 3 = 1)
    (hy3 : y ^ 3 = 1) (hz3 : z ^ 3 = 1) (hxJ : π x ∈ J) (hyJ : π y ∈ J) (hzJ : π z ∈ J)
    (hind : ∀ a b c : ℕ, x ^ a * y ^ b * z ^ c ∈ π.ker → 3 ∣ a ∧ 3 ∣ b ∧ 3 ∣ c) :
    3 ≤ CFSG.Open.pRank 3 J := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set x' : ↥J := ⟨π x, hxJ⟩
  set y' : ↥J := ⟨π y, hyJ⟩
  set z' : ↥J := ⟨π z, hzJ⟩
  have hker : ∀ a b c : ℕ, π x ^ a * π y ^ b * π z ^ c = 1 → 3 ∣ a ∧ 3 ∣ b ∧ 3 ∣ c :=
    fun a b c h => hind a b c (by rw [MonoidHom.mem_ker, map_mul, map_mul, map_pow, map_pow,
      map_pow, h])
  have hπ3 : ∀ w : K, w ^ 3 = 1 → π w ^ 3 = 1 := fun w hw => by rw [← map_pow, hw, map_one]
  refine (three_le_pRank_of_gens (G := ↥J) (p := 3) (x := x') (y := y') (z := z')
    (Subtype.ext (hπ3 x hx3)) (Subtype.ext (hπ3 y hy3)) (Subtype.ext (hπ3 z hz3))
    (Subtype.ext (by simp [x', y', ← map_mul, hxy.eq])) (Subtype.ext (by
      simp [x', z', ← map_mul, hxz.eq])) (Subtype.ext (by simp [y', z', ← map_mul, hyz.eq]))
    ?_ ?_ ?_).trans (RealThreeRank.pRank_top_subtype_le 3 (by norm_num) J)
  · intro h
    have h1 : π x = 1 := congrArg Subtype.val h
    have := (hker 1 0 0 (by simp [h1])).1
    omega
  · intro n h
    have h1 : π x ^ n = π y := congrArg Subtype.val h
    have h2 : π x ^ n * π y ^ 2 * π z ^ 0 = 1 := by
      rw [h1, pow_zero, mul_one, ← pow_succ', hπ3 y hy3]
    have := (hker n 2 0 h2).2.1
    omega
  · intro n m h
    have h1 : π x ^ n * π y ^ m = π z := congrArg Subtype.val h
    have h2 : π x ^ n * π y ^ m * π z ^ 2 = 1 := by
      rw [h1, ← pow_succ', hπ3 z hz3]
    have := (hker n m 2 h2).2.2
    omega

end Rank

theorem three_dvd_of_conj_eq_inv {g w : G} (hg : g ^ 3 = 1) (hg1 : g ≠ 1)
    (hw : w * g * w⁻¹ = g⁻¹) {a : ℕ} (ha : w * g ^ a * w⁻¹ = g ^ a) : 3 ∣ a := by
  have h1 : w * g ^ a * w⁻¹ = (g ^ a)⁻¹ := by
    rw [← inv_pow, ← hw, conj_pow]
  have h2' : g ^ a = (g ^ a)⁻¹ := ha.symm.trans h1
  have h2 : g ^ (2 * a) = 1 := by
    rw [pow_mul', sq]
    nth_rewrite 2 [h2']
    exact mul_inv_cancel _
  have h3 := orderOf_dvd_of_pow_eq_one h2
  rw [orderOf_eq_prime hg hg1] at h3
  omega

theorem three_dvd_of_torus_eqs {K : Type*} [Field K] {ω : Kˣ} (hω : orderOf ω = 3) {p q r : ℕ}
    (h1 : ω ^ p = ω⁻¹ ^ p * ω ^ q) (h2 : ω⁻¹ ^ p * ω ^ q = ω⁻¹ ^ q * ω ^ r)
    (h3 : ω⁻¹ ^ q * ω ^ r = ω⁻¹ ^ r) : 3 ∣ p ∧ 3 ∣ q ∧ 3 ∣ r := by
  have hω3 : ω ^ 3 = 1 := by rw [← hω]; exact pow_orderOf_eq_one ω
  have hi : ω⁻¹ = ω ^ 2 := by
    rw [inv_eq_iff_mul_eq_one, ← pow_succ']
    exact hω3
  simp only [hi, ← pow_mul, ← pow_add] at h1 h2 h3
  have e1 := pow_eq_pow_iff_modEq.1 h1
  have e2 := pow_eq_pow_iff_modEq.1 h2
  have e3 := pow_eq_pow_iff_modEq.1 h3
  rw [hω] at e1 e2 e3
  simp only [Nat.ModEq] at e1 e2 e3
  omega

end Generic

section Levi

open CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.AGLEmbeddingD2.ParabLevi

variable {K : Type*} [Group K]

theorem leviM_mono {D : UniversalRootDatum K} {I S : Set (Fin D.rank)} (h : I ⊆ S) :
    leviM D I ≤ leviM D S :=
  iSup₂_le fun i hi => le_iSup₂_of_le (f := fun i (_ : i ∈ S) => rankOne D.rootGroup i) i (h hi)
    le_rfl

theorem leviM_pair (D : UniversalRootDatum K) (a b : Fin D.rank) :
    leviM D {a, b} = rankOne D.rootGroup a ⊔ rankOne D.rootGroup b := by
  unfold leviM
  rw [iSup_insert, iSup_singleton]

end Levi

section Torus

open CFSG.LieType.Universal CFSG.LieType.Universal.Unitary CFSG.LieType.Universal.Unitary.SUExtras
  CFSG.LieType.CurtisTits Matrix

variable {F : Type} [Field F] {σ : F ≃+* F} {n : ℕ}

theorem tFun_pow (k : Fin (n / 2)) {c : F} (hc : c ≠ 0) (m : ℕ) :
    tFun σ k c ^ m = tFun σ k (c ^ m) := by
  induction m with
  | zero => rw [pow_zero, pow_zero, tFun_one]
  | succ m ih => rw [pow_succ, ih, pow_succ, tFun_mul k (pow_ne_zero m hc) hc]

theorem tFun_lowIdx (k : Fin (n / 2)) (c : F) : tFun σ k c (lowIdx k) = c := by
  by_cases hk : k.val + 1 < n / 2
  · unfold tFun
    rw [dite_eq_left hk]
    exact shortTorusFun_left _ _ _
  · exact tFun_lowIdx_of_last hk c

theorem tFun_succ_idx {a : Fin (n / 2)} (ha : a.val + 1 < n / 2) (c : F) :
    tFun σ a c (lowIdx ⟨a.val + 1, ha⟩) = c⁻¹ := by
  simp only [tFun, ha, dite_true]
  exact shortTorusFun_right (lowIdx_ne_succ ha) c

theorem tFun_rev_succ_idx {a : Fin (n / 2)} (ha : a.val + 1 < n / 2) (c : F) :
    tFun σ a c (Fin.rev (lowIdx ⟨a.val + 1, ha⟩)) = σ c := by
  have ha' := a.isLt
  simp only [tFun, ha, dite_true, shortTorusFun, lowIdx, Fin.ext_iff, Fin.val_rev]
  split_ifs <;> first | rfl | omega

theorem tFun_apply_lowIdx_short {k : Fin (n / 2)} (hk : k.val + 1 < n / 2) (i : Fin (n / 2))
    (c : F) :
    tFun σ k c (lowIdx i) =
      if i.val = k.val then c else if i.val = k.val + 1 then c⁻¹ else 1 := by
  have hi := i.isLt
  have hk' := k.isLt
  simp only [tFun, hk, dite_true, shortTorusFun, lowIdx, Fin.ext_iff, Fin.val_rev]
  split_ifs <;> first | rfl | omega

theorem levelPerm_lowIdx {k : Fin (n / 2)} (hk : k.val + 1 < n / 2) :
    levelPerm k (lowIdx k) = lowIdx (n := n) ⟨k.val + 1, hk⟩ := by
  rw [levelPerm, dite_eq_left hk, Equiv.Perm.mul_apply,
    Equiv.swap_apply_of_ne_of_ne (lowIdx_ne_rev k k) (lowIdx_ne_rev _ _), Equiv.swap_apply_left]

theorem levelPerm_lowIdx_succ {k : Fin (n / 2)} (hk : k.val + 1 < n / 2) :
    levelPerm k (lowIdx (n := n) ⟨k.val + 1, hk⟩) = lowIdx k := by
  rw [levelPerm, dite_eq_left hk, Equiv.Perm.mul_apply,
    Equiv.swap_apply_of_ne_of_ne (lowIdx_ne_rev (⟨k.val + 1, hk⟩ : Fin (n / 2)) k)
      (lowIdx_ne_rev (⟨k.val + 1, hk⟩ : Fin (n / 2)) ⟨k.val + 1, hk⟩), Equiv.swap_apply_right]

theorem levelWeyl_conj_short_torus (hσ : ∀ c, σ (σ c) = c) {ζ : traceZero σ} (hζ : (ζ : F) ≠ 0)
    {a : Fin (n / 2)} (ha : a.val + 1 < n / 2) {x : SU σ n} {c : Fˣ}
    (hxm : mat σ n x = diagonal (tFun σ a (c : F))) :
    levelWeyl hσ ζ a * x * (levelWeyl hσ ζ a)⁻¹ = x⁻¹ := by
  apply mat_injective
  have hconj := coe_conj_diagonal (coe_levelWeyl hσ hζ a) hxm
  rw [levelPerm_symm] at hconj
  rw [mat_apply, hconj, diagonal_inv_eq (tFun_ne_zero a c.ne_zero) hxm]
  congr 1
  funext r
  rw [← congrFun (tFun_inv a (c : F)) r, ← Units.val_inv_eq_inv_val]
  simp only [tFun, ha, dite_true]
  exact shortTorusFun_levelPerm_self ha c r

theorem diag_levelPerm_of_central (hσ : ∀ c, σ (σ c) = c) {ζ : traceZero σ} (hζ : (ζ : F) ≠ 0)
    {w : SU σ n} (hw : w ∈ Subgroup.center (SU σ n)) {d : Fin n → F}
    (hd : mat σ n w = diagonal d) (k : Fin (n / 2)) (s : Fin n) : d (levelPerm k s) = d s := by
  have hconj := coe_conj_diagonal (coe_levelWeyl hσ hζ k) hd
  rw [levelPerm_symm] at hconj
  have hc : levelWeyl hσ ζ k * w * (levelWeyl hσ ζ k)⁻¹ = w := by
    rw [mul_inv_eq_iff_eq_mul]
    exact Subgroup.mem_center_iff.mp hw (levelWeyl hσ ζ k)
  rw [hc] at hconj
  have := congrArg (fun M : Matrix (Fin n) (Fin n) F => M s s) (hconj.symm.trans hd)
  simpa using this

theorem torus_triple_dvd_of_central (hσ : ∀ c, σ (σ c) = c) {ζ : traceZero σ} (hζ : (ζ : F) ≠ 0)
    {a b c : Fin (n / 2)} (ha : a.val = 0) (hb : b.val = 1) (hc : c.val = 2) (h3 : 3 < n / 2)
    {ω : Fˣ} (hω : orderOf ω = 3) {x y z : SU σ n}
    (hxm : mat σ n x = diagonal (tFun σ a (ω : F))) (hym : mat σ n y = diagonal (tFun σ b (ω : F)))
    (hzm : mat σ n z = diagonal (tFun σ c (ω : F))) {p q r : ℕ}
    (hw : x ^ p * y ^ q * z ^ r ∈ Subgroup.center (SU σ n)) : 3 ∣ p ∧ 3 ∣ q ∧ 3 ∣ r := by
  have ha1 : a.val + 1 < n / 2 := by omega
  have hb1 : b.val + 1 < n / 2 := by omega
  have hc1 : c.val + 1 < n / 2 := by omega
  set e : Fin (n / 2) := ⟨3, h3⟩ with he
  have hd : mat σ n (x ^ p * y ^ q * z ^ r) =
      diagonal (fun s => tFun σ a (ω : F) s ^ p * tFun σ b (ω : F) s ^ q *
        tFun σ c (ω : F) s ^ r) := by
    rw [map_mul, map_mul, map_pow, map_pow, map_pow, hxm, hym, hzm, diagonal_pow, diagonal_pow,
      diagonal_pow, diagonal_mul_diagonal, diagonal_mul_diagonal]
    rfl
  have key := diag_levelPerm_of_central hσ hζ hw hd
  have eab : (⟨a.val + 1, ha1⟩ : Fin (n / 2)) = b := Fin.ext (by simp [ha, hb])
  have ebc : (⟨b.val + 1, hb1⟩ : Fin (n / 2)) = c := Fin.ext (by simp [hb, hc])
  have ecd : (⟨c.val + 1, hc1⟩ : Fin (n / 2)) = e := Fin.ext (by simp [hc, he])
  have k1 := key a (lowIdx a)
  have k2 := key b (lowIdx b)
  have k3 := key c (lowIdx c)
  rw [levelPerm_lowIdx ha1, eab] at k1
  rw [levelPerm_lowIdx hb1, ebc] at k2
  rw [levelPerm_lowIdx hc1, ecd] at k3
  simp only [tFun_apply_lowIdx_short ha1, tFun_apply_lowIdx_short hb1,
    tFun_apply_lowIdx_short hc1, ha, hb, hc, he] at k1 k2 k3
  norm_num at k1 k2 k3
  refine three_dvd_of_torus_eqs hω ?_ ?_ ?_
  · apply Units.ext
    simpa [Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val, inv_pow] using k1.symm
  · apply Units.ext
    simpa [Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val, inv_pow] using k2.symm
  · apply Units.ext
    simpa [Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val, inv_pow] using k3.symm

theorem commute_diagonal_of_isBlk {blk : Fin n → ℕ} {M : Matrix (Fin n) (Fin n) F}
    (hM : IsBlk blk M) {d : Fin n → F} (hd : ∀ s t, blk s = blk t → blk s ≠ 0 → d s = d t) :
    diagonal d * M = M * diagonal d := by
  ext s t
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases hst : blk s = blk t ∧ blk s ≠ 0
  · rw [hd s t hst.1 hst.2, mul_comm]
  · rw [hM s t hst]
    by_cases h : s = t
    · subst h
      rw [mul_comm]
    · rw [Matrix.one_apply_ne h, mul_zero, zero_mul]

theorem commute_of_diag_eq_last (hσ : ∀ c, σ (σ c) = c) (he : Even n) {c : Fin (n / 2)}
    (hc : ¬ c.val + 1 < n / 2) {d : Fin n → F} (hd : d (lowIdx c) = d (Fin.rev (lowIdx c)))
    {x : SU σ n} (hxd : mat σ n x = diagonal d) {t : SU σ n}
    (ht : t ∈ rankOne (rootGroup σ hσ n) c) : x * t = t * x := by
  apply mat_injective
  rw [map_mul, map_mul, hxd]
  refine commute_diagonal_of_isBlk (isBlk_last_of_mem hc ht) fun s t hst hne => ?_
  have hmem : ∀ u : Fin n, blkLast c u ≠ 0 → u = lowIdx c ∨ u = Fin.rev (lowIdx c) := by
    intro u hu
    rcases (blkLast_eq_one_iff u).1 (blkLast_eq_one_of_ne_zero hu) with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exfalso
      obtain ⟨r, hr⟩ := he
      have h1 := congrArg Fin.val h
      have := u.isLt
      simp only [Fin.val_rev] at h1
      omega
  rcases hmem s hne with rfl | rfl <;> rcases hmem t (hst ▸ hne) with rfl | rfl
  · rfl
  · exact hd
  · exact hd.symm
  · rfl

end Torus

section Block

open CFSG.LieType.Universal CFSG.LieType.Universal.Unitary CFSG.LieType.Universal.Unitary.SUExtras
  CFSG.LieType.CurtisTits CFSG.LieType.BorelTits Matrix

variable {F : Type} [Field F] {σ : F ≃+* F} {n : ℕ}

@[expose] def blk2 (t : ℕ) (s : Fin n) : ℕ := if s.val < t then 1 else 2

theorem isBlk_mono {b₁ b₂ : Fin n → ℕ} {M : Matrix (Fin n) (Fin n) F} (hM : IsBlk b₁ M)
    (h : ∀ a b, b₁ a = b₁ b → b₁ a ≠ 0 → b₂ a = b₂ b ∧ b₂ a ≠ 0) : IsBlk b₂ M :=
  fun a b hab => hM a b fun ⟨h1, h2⟩ => hab (h a b h1 h2)

variable [Finite F]

@[expose] noncomputable def blkSub (blk : Fin n → ℕ) : Subgroup (SU σ n) where
  carrier := {g | IsBlk blk (mat σ n g)}
  mul_mem' := fun {a b} ha hb => by
    show IsBlk blk (mat σ n (a * b))
    rw [map_mul]
    exact ha.mul hb
  one_mem' := by
    show IsBlk blk (mat σ n 1)
    rw [map_one]
    exact isBlk_one _
  inv_mem' := fun {g} hg => by
    have hpow : ∀ m : ℕ, IsBlk blk (mat σ n (g ^ m)) := fun m => by
      induction m with
      | zero => rw [pow_zero, map_one]; exact isBlk_one _
      | succ m ih => rw [pow_succ, map_mul]; exact ih.mul hg
    have hinv : g⁻¹ = g ^ (orderOf g - 1) := by
      have hpos := orderOf_pos g
      rw [inv_eq_iff_mul_eq_one, ← pow_succ', Nat.sub_add_cancel hpos, pow_orderOf_eq_one]
    show IsBlk blk (mat σ n g⁻¹)
    rw [hinv]
    exact hpow _

@[expose] noncomputable def resMat (t : ℕ) (ht : t ≤ n) :
    blkSub (σ := σ) (n := n) (blk2 t) →* Matrix (Fin t) (Fin t) F where
  toFun g := Matrix.of fun i j => mat σ n g (Fin.castLE ht i) (Fin.castLE ht j)
  map_one' := by
    ext i j
    change mat σ n 1 (Fin.castLE ht i) (Fin.castLE ht j) = _
    rw [map_one]
    simp [Matrix.one_apply]
  map_mul' g h := by
    ext i j
    change mat σ n ((g : SU σ n) * h) (Fin.castLE ht i) (Fin.castLE ht j) = _
    rw [map_mul, Matrix.mul_apply, Matrix.mul_apply]
    simp only [Matrix.of_apply]
    refine (Fintype.sum_of_injective (Fin.castLE ht) (Fin.castLE_injective ht) _ _ ?_
      (fun u => rfl)).symm
    intro s hs
    have hs' : ¬ s.val < t := fun hlt => hs ⟨⟨s.val, hlt⟩, Fin.ext rfl⟩
    have hij : (Fin.castLE ht i) ≠ s := fun he => hs' (by
      rw [← he]
      exact i.isLt)
    rw [g.2 (Fin.castLE ht i) s (fun ⟨h1, _⟩ => by simp [blk2, hs', i.isLt] at h1),
      Matrix.one_apply_ne hij, zero_mul]

@[expose] noncomputable def resGL (t : ℕ) (ht : t ≤ n) :
    blkSub (σ := σ) (n := n) (blk2 t) →* GL (Fin t) F :=
  (resMat t ht).toHomUnits

theorem resGL_injective {t : ℕ} (hn : n = 2 * t) :
    Function.Injective (resGL (σ := σ) (n := n) t (by omega)) := by
  have ht : t ≤ n := by omega
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro g hg
  rw [Subgroup.mem_bot]
  have hres : ∀ i j : Fin t, mat σ n g (Fin.castLE ht i) (Fin.castLE ht j) =
      (1 : Matrix (Fin t) (Fin t) F) i j := by
    intro i j
    have h1 : resMat (σ := σ) (n := n) t ht g = 1 := by
      have := congrArg Units.val (MonoidHom.mem_ker.mp hg)
      simpa [resGL] using this
    have := congrFun (congrFun h1 i) j
    simpa [resMat] using this
  have hblk : IsBlk (blk2 t) (mat σ n g) := g.2
  have hcol : ∀ s : Fin n, s.val < t → ∀ a,
      mat σ n g a s = (1 : Matrix (Fin n) (Fin n) F) a s := by
    intro s hs a
    by_cases ha : a.val < t
    · have := hres ⟨a.val, ha⟩ ⟨s.val, hs⟩
      simpa [Matrix.one_apply, Fin.ext_iff] using this
    · exact hblk a s (fun ⟨h1, _⟩ => by simp [blk2, ha, hs] at h1)
  refine Subtype.ext (mat_injective ?_)
  rw [Subgroup.coe_one, map_one]
  ext a b
  by_cases ha : a.val < t
  · by_cases hb : b.val < t
    · have := hres ⟨a.val, ha⟩ ⟨b.val, hb⟩
      simpa [Matrix.one_apply, Fin.ext_iff] using this
    · exact hblk a b (fun ⟨h1, _⟩ => by simp [blk2, ha, hb] at h1)
  · have hs : (Fin.rev a).val < t := by
      have := a.isLt
      simp only [Fin.val_rev]
      omega
    have := mat_rev_apply_of_col (hcol (Fin.rev a) hs) b
    rwa [Fin.rev_rev] at this

theorem blk2_eq_blkShort {k : Fin (n / 2)} (hk : k.val + 1 < n / 2) {t : ℕ} (hn : n = 2 * t)
    (ht : k.val + 1 < t) {s : Fin n} (hs : blkShort k hk s ≠ 0) :
    blk2 t s = blkShort k hk s := by
  have hk' := k.isLt
  unfold blkShort at hs ⊢
  unfold blk2
  by_cases h1 : s = lowIdx k ∨ s = lowIdx ⟨k.val + 1, hk⟩
  · rw [ite_eq_left h1]
    have : s.val < t := by
      rcases h1 with rfl | rfl <;> simp only [lowIdx] <;> omega
    rw [ite_eq_left this]
  · rw [ite_eq_right h1] at hs ⊢
    by_cases h2 : s = Fin.rev (lowIdx k) ∨ s = Fin.rev (lowIdx ⟨k.val + 1, hk⟩)
    · have : ¬ s.val < t := by
        rcases h2 with rfl | rfl <;> simp only [lowIdx, Fin.val_rev] <;> omega
      rw [ite_eq_left h2, ite_eq_right this]
    · rw [ite_eq_right h2] at hs
      exact absurd rfl hs

end Block

section SU

open CFSG.LieType.Universal CFSG.LieType.Universal.Unitary CFSG.LieType.Universal.Unitary.SUExtras
  CFSG.LieType.CurtisTits CFSG.LieType.RootSystem CFSG.LieType.Steinberg CFSG.AGLEmbedding
  CFSG.AGLEmbedding.ParabHub CFSG.AGLEmbedding.ParabPrime CFSG.AGLEmbeddingD2.ParabLevi
  CFSG.AGLEmbeddingD2.ParabRankEngine CFSG.AGLEmbeddingD2.SquareGeneric CFSG.LieType.BorelTits
  CFSG.AGLEmbedding.ToralCensus CFSG.AGLEmbeddingD2.ParabRealThree Matrix

variable {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ} (hF : Nat.card F = (2 ^ f) ^ 2)
  {n : ℕ}

theorem cartan_eq_zero_of_two_le {a b : Fin (n / 2)} (hab : a.val + 2 ≤ b.val) :
    (rootDatum hF n).cartan a b = 0 := by
  change CFSG.LieType.Universal.Unitary.cartan n a b = 0
  unfold CFSG.LieType.Universal.Unitary.cartan
  have h1 : a ≠ b := fun h => by rw [h] at hab; omega
  have h2 : ¬ (a.val + 1 = b.val ∨ b.val + 1 = a.val) := by omega
  have h3 : ¬ (b.val + 1 = a.val ∨ a.val + 1 = b.val) := by omega
  split_ifs
  · simp only [Symplectic.cartanC, Matrix.of_apply, h1, h2, ite_false]
  · simp only [Matrix.transpose_apply, Symplectic.cartanC, Matrix.of_apply, h1.symm, h3,
      ite_false]

include hF in
theorem cartan_last_two (he : Even n) {b c : Fin (n / 2)} (hc : c.val + 1 = n / 2)
    (hb : b.val + 2 = n / 2) :
    (rootDatum hF n).cartan c b = -1 ∧ (rootDatum hF n).cartan b c = -2 := by
  have hcb : c ≠ b := fun h => by rw [h] at hc; omega
  change CFSG.LieType.Universal.Unitary.cartan n c b = -1 ∧
    CFSG.LieType.Universal.Unitary.cartan n b c = -2
  unfold CFSG.LieType.Universal.Unitary.cartan
  rw [ite_eq_left he]
  simp only [Symplectic.cartanC, Matrix.of_apply]
  constructor
  · split_ifs <;> simp_all <;> omega
  · split_ifs <;> simp_all
    omega

include hF in
theorem card_ker_eq_gcd (hn : 1 ≤ n) {Y : Type} [Group Y]
    (e : Y ≃* StatedProj (StatedSU n (2 ^ f) F)) :
    Nat.card (e.symm.toMonoidHom.comp ((QuotientGroup.mk' _).comp
      (equivStatedSU hF n).toMonoidHom)).ker = Nat.gcd n (2 ^ f + 1) := by
  set ψ := equivStatedSU hF n
  set N := (StatedScalars (Fin n) F).subgroupOf (StatedSU n (2 ^ f) F)
  have hker : (e.symm.toMonoidHom.comp ((QuotientGroup.mk' N).comp ψ.toMonoidHom)).ker =
      N.comap ψ.toMonoidHom := by
    ext z
    simp only [MonoidHom.mem_ker, MonoidHom.coe_comp, Function.comp_apply,
      MulEquiv.coe_toMonoidHom, map_eq_one_iff _ e.symm.injective, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, Subgroup.mem_comap]
  rw [hker, ← (CFSG.LinearGroups.unitary_scalar_kernel Nat.prime_two hF hn).2.2]
  exact Nat.card_congr (ψ.toEquiv.subtypeEquiv fun z => Iff.rfl)

include hF in
theorem coprime_three_card_ker (hn : 1 ≤ n) {Y : Type} [Group Y]
    (e : Y ≃* StatedProj (StatedSU n (2 ^ f) F)) (h : ¬ 3 ∣ n ∨ ¬ 3 ∣ 2 ^ f + 1) :
    Nat.Coprime 3 (Nat.card (e.symm.toMonoidHom.comp ((QuotientGroup.mk' _).comp
      (equivStatedSU hF n).toMonoidHom)).ker) := by
  rw [card_ker_eq_gcd hF hn e]
  rcases h with h | h
  · exact ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h).coprime_dvd_right
      (Nat.gcd_dvd_left _ _)
  · exact ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h).coprime_dvd_right
      (Nat.gcd_dvd_right _ _)

omit [CharP F 2] in
include hF in
theorem one_lt_two_pow : 1 < 2 ^ f := by
  have h1 : 1 < Nat.card F := Finite.one_lt_card
  rw [hF] at h1
  by_contra h
  have h2 : 2 ^ f ≤ 1 := not_lt.mp h
  nlinarith [Nat.zero_le (2 ^ f)]

omit [CharP F 2] in
include hF in
theorem four_le_card : 4 ≤ Nat.card F := by
  have := one_lt_two_pow hF
  rw [hF]
  nlinarith

omit [CharP F 2] in
include hF in
theorem exists_order_three : ∃ ω : Fˣ, ω ^ 3 = 1 ∧ ω ≠ 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hd : 3 ∣ Nat.card F - 1 := by
    have h4 : (2 ^ f) ^ 2 = 4 ^ f := by
      rw [← pow_mul, mul_comm, pow_mul]
      norm_num
    rw [hF, h4]
    simpa using Nat.sub_dvd_pow_sub_pow 4 1 f
  obtain ⟨ω, hω⟩ := SquareLinear.exists_orderOf_eq_three hd
  exact ⟨ω, by rw [← hω, pow_orderOf_eq_one], fun h => by
    rw [h, orderOf_one] at hω
    omega⟩

theorem unitaryInvolution_eq_pow_of_pow_three {ω : Fˣ} (hω3 : ω ^ 3 = 1) :
    unitaryInvolution F 2 f (ω : F) = ((ω ^ (2 ^ f % 3) : Fˣ) : F) := by
  rw [unitaryInvolution_apply, ← Units.val_pow_eq_pow_val, pow_eq_pow_mod _ hω3]

theorem unitaryInvolution_eq_self_of_pow_three {ω : Fˣ} (hω3 : ω ^ 3 = 1) (hf : Even f) :
    unitaryInvolution F 2 f (ω : F) = ω := by
  rw [unitaryInvolution_eq_pow_of_pow_three hω3, two_pow_mod_three_of_even hf, pow_one]

theorem unitaryInvolution_eq_inv_of_pow_three {ω : Fˣ} (hω3 : ω ^ 3 = 1) (hf : Odd f) :
    unitaryInvolution F 2 f (ω : F) = ((ω⁻¹ : Fˣ) : F) := by
  rw [unitaryInvolution_eq_pow_of_pow_three hω3, two_pow_mod_three_of_odd hf]
  congr 1
  rw [eq_inv_iff_mul_eq_one, ← pow_succ, hω3]

include hF in
theorem exists_norm_eq_of_fixed' (x : F) (hx : unitaryInvolution F 2 f x = x) :
    ∃ b, unitaryInvolution F 2 f b * b = x := by
  by_cases hx0 : x = 0
  · exact ⟨0, by simp [hx0]⟩
  · exact CFSG.ClassicalGroups.Unitary.exists_norm_eq_of_fixed hF hx hx0

include hF in
theorem exists_mem_levelTorus (a : Fin (n / 2)) (c : Fˣ)
    (hc : ¬ a.val + 1 < n / 2 → Even n → unitaryInvolution F 2 f (c : F) = c) :
    ∃ x ∈ levelTorus (unitaryInvolution F 2 f) a,
      mat (unitaryInvolution F 2 f) n x =
        diagonal (tFun (unitaryInvolution F 2 f) a (c : F)) := by
  have hσ := unitaryInvolution_involutive hF
  obtain ⟨ζ, hζ⟩ := exists_traceZero_ne_zero hF
  by_cases hk : a.val + 1 < n / 2
  · refine ⟨shortTorus _ hσ (lowIdx_ne_succ hk) (lowIdx_ne_rev a a) (lowIdx_ne_rev _ _) (c : F),
      shortTorus_mem_levelTorus hσ hk c, ?_⟩
    rw [mat_apply, coe_shortTorus _ hσ _ _ _ (lowIdx_ne_rev _ _) c.ne_zero]
    unfold tFun
    rw [dite_eq_left hk]
  · by_cases he : Even n
    · have hce := hc hk he
      refine ⟨longTorus _ (lowIdx_ne_rev a a) ζ hce, longTorus_mem_levelTorus hk hζ c hce, ?_⟩
      rw [mat_apply, coe_longTorus _ _ hζ hce c.ne_zero]
      unfold tFun
      rw [dite_eq_right hk, ite_eq_left he]
    · obtain ⟨g, -, hg⟩ :=
        exists_heisGen_mem_rankOne hσ hζ (exists_norm_eq_of_fixed' hF) hk he c
      refine ⟨g, heisGen_mem_levelTorus hk he c hg, ?_⟩
      rw [mat_apply, hg]
      unfold tFun
      rw [dite_eq_right hk, ite_eq_right he]

include hF in
theorem exists_levelTorus_order_three (a : Fin (n / 2)) (ω : Fˣ) (hω3 : ω ^ 3 = 1)
    (hω1 : ω ≠ 1)
    (hc : ¬ a.val + 1 < n / 2 → Even n → unitaryInvolution F 2 f (ω : F) = ω) :
    ∃ x ∈ levelTorus (unitaryInvolution F 2 f) a,
      mat (unitaryInvolution F 2 f) n x = diagonal (tFun (unitaryInvolution F 2 f) a (ω : F)) ∧
        x ^ 3 = 1 ∧ x ≠ 1 := by
  obtain ⟨x, hxH, hxm⟩ := exists_mem_levelTorus hF a ω hc
  refine ⟨x, hxH, hxm, mat_injective ?_, fun h => hω1 ?_⟩
  · rw [map_pow, hxm, diagonal_pow, tFun_pow a ω.ne_zero, map_one, ← Units.val_pow_eq_pow_val,
      hω3, Units.val_one, tFun_one]
    exact diagonal_one
  · have := congrArg (fun y => mat (unitaryInvolution F 2 f) n y (lowIdx a) (lowIdx a)) h
    simp only [hxm, diagonal_apply_eq, tFun_lowIdx, map_one, one_apply_eq] at this
    exact Units.ext this

include hF in
theorem realThreeOver_torus_su {Y : Type*} [Group Y] {π : SU (unitaryInvolution F 2 f) n →* Y}
    {J : Subgroup Y}
    (hBJ : borel (rootDatum hF n) (levelTorus (unitaryInvolution F 2 f)) ≤ J.comap π)
    {a : Fin (n / 2)} (ha : a.val + 1 < n / 2) {ω : Fˣ} (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1) :
    RealThreeOver π (rankOne (rootDatum hF n).rootGroup a) J := by
  have hσ := unitaryInvolution_involutive hF
  obtain ⟨ζ, hζ⟩ := exists_traceZero_ne_zero hF
  obtain ⟨x, hxH, hxm, hx3, hx1⟩ :=
    exists_levelTorus_order_three hF a ω hω3 hω1 (fun h => absurd ha h)
  have hxL : x ∈ rankOne (rootDatum hF n).rootGroup a :=
    levelTorus_le_rankOne hσ hζ (exists_norm_eq_of_fixed' hF) a hxH
  have hperf : ⁅rankOne (rootDatum hF n).rootGroup a, rankOne (rootDatum hF n).rootGroup a⁆ =
      rankOne (rootDatum hF n).rootGroup a := by
    have : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) F) :=
      sl2_isPerfect (four_le_card hF)
    have hperfL : Group.IsPerfect ↥(rankOne (rootDatum hF n).rootGroup a) :=
      Group.IsPerfect.ofSurjective
        (f := (rankOneShortEquiv (hσ := hσ) ha).symm.toMonoidHom)
        (rankOneShortEquiv (hσ := hσ) ha).symm.surjective
    exact commutator_eq_self_of_isPerfect hperfL
  refine ⟨x, by rw [hperf]; exact hxL,
    hBJ (le_sup_left (a := ⨆ k, levelTorus (unitaryInvolution F 2 f) k)
      (le_iSup (levelTorus (unitaryInvolution F 2 f)) a hxH)), hx3, ?_, levelWeyl hσ ζ a,
    levelWeyl_mem_rankOne hσ ζ a, levelWeyl_conj_short_torus hσ hζ ha hxm⟩
  intro hz
  have hpq : lowIdx a ≠ lowIdx (n := n) ⟨a.val + 1, ha⟩ := lowIdx_ne_succ ha
  have hqp : lowIdx (n := n) ⟨a.val + 1, ha⟩ ≠ Fin.rev (lowIdx a) := lowIdx_ne_rev _ _
  have hc := Subgroup.mem_center_iff.mp hz
    (rootHom _ hσ hpq (lowIdx_ne_rev a a) (lowIdx_ne_rev _ _) (Multiplicative.ofAdd (1 : F)))
  have h1 := congrArg (fun z => mat (unitaryInvolution F 2 f) n z (lowIdx a)
    (lowIdx (n := n) ⟨a.val + 1, ha⟩)) hc
  simp only [map_mul, hxm, mat_apply, coe_rootHom, toAdd_ofAdd, Matrix.mul_diagonal,
    Matrix.diagonal_mul, rootMatrix_apply_pq hpq hqp, tFun_lowIdx, tFun_succ_idx ha, mul_one,
    one_mul] at h1
  have h2 : ω * ω = 1 := Units.ext (by
    rw [Units.val_mul, Units.val_one]
    nth_rewrite 1 [← h1]
    exact inv_mul_cancel₀ ω.ne_zero)
  apply hω1
  calc ω = ω ^ 3 * (ω * ω)⁻¹ := by group
    _ = 1 := by rw [hω3, h2, inv_one, one_mul]

include hF in
theorem isCyclic_of_isPGroup_three_rankOne (hf : Even f) (i : Fin (n / 2))
    {P : Subgroup (SU (unitaryInvolution F 2 f) n)}
    (hP : P ≤ rankOne (rootDatum hF n).rootGroup i) (h3 : IsPGroup 3 P) : IsCyclic P := by
  have hσ := unitaryInvolution_involutive hF
  have h2 := one_lt_two_pow hF
  have hmod := two_pow_mod_three_of_even hf
  have h4 : 4 ≤ 2 ^ f := by
    obtain ⟨k, hk⟩ := hf
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · simp at hk
      subst hk
      simp at h2
    · calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) (by omega)
  by_cases hk : i.val + 1 < n / 2
  · exact isCyclic_of_le_of_equiv (rankOneShortEquiv (hσ := hσ) hk)
      (fun Q hQ => SquareLinear.isCyclic_of_isPGroup_three_sl2 (four_le_card hF) Q hQ) hP h3
  · by_cases he : Even n
    · obtain ⟨ζ, hζ0, hζ⟩ := exists_unitaryInvolution_eq_neg hF
      have hcard : 4 ≤ Nat.card (fixedSubfield F 2 f) := by
        rw [card_fixedSubfield hF]
        exact h4
      exact isCyclic_of_le_of_equiv
        ((rankOneLastEvenEquiv hF he hk).trans (hypEquiv hζ0 hζ).symm)
        (fun Q hQ => SquareLinear.isCyclic_of_isPGroup_three_sl2 hcard Q hQ) hP h3
    · have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      refine isCyclic_of_le_of_equiv ((rankOneLastOddEquiv hF he hk).trans (equivStatedSU hF 3))
        (fun Q hQ => ?_) hP h3
      obtain ⟨S, hS⟩ := hQ.exists_le_sylow
      have hre : ¬ 3 ∣ 2 ^ f + 1 := by omega
      have : IsCyclic (S : Subgroup (StatedSU 3 (2 ^ f) F)) :=
        CFSG.ClassicalInvolution.ModelFacts.OddCover.statedSU_three_isCyclic_sylow hF
          (by norm_num) (by norm_num) hre S
      exact Subgroup.isCyclic_of_le hS

include hF in
theorem eq_bot_of_isPGroup_five_rankOne_last_even (hf : Odd f) (he : Even n) {i : Fin (n / 2)}
    (hk : ¬ i.val + 1 < n / 2) {P : Subgroup (SU (unitaryInvolution F 2 f) n)}
    (hP : P ≤ rankOne (rootDatum hF n).rootGroup i) (h5 : IsPGroup 5 P) : P = ⊥ := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨ζ, hζ0, hζ⟩ := exists_unitaryInvolution_eq_neg hF
  have := Fintype.ofFinite (fixedSubfield F 2 f)
  have hcard : Fintype.card (fixedSubfield F 2 f) = 2 ^ f := by
    rw [← Nat.card_eq_fintype_card, card_fixedSubfield hF]
  exact eq_bot_of_le_of_equiv ((rankOneLastEvenEquiv hF he hk).trans (hypEquiv hζ0 hζ).symm)
    (fun Q hQ => CyclicSylowGL.eq_bot_of_isPGroup_five_of_injective_GL_two_pow hf hcard
      (by norm_num) Matrix.SpecialLinearGroup.toGL Matrix.SpecialLinearGroup.toGL_injective Q hQ)
    hP h5

include hF in
theorem isCyclic_of_isPGroup_five_rankOne (hf : Odd f) (i : Fin (n / 2))
    {P : Subgroup (SU (unitaryInvolution F 2 f) n)}
    (hP : P ≤ rankOne (rootDatum hF n).rootGroup i) (h5 : IsPGroup 5 P) : IsCyclic P := by
  have hσ := unitaryInvolution_involutive hF
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have := Fintype.ofFinite F
  have hk4 : Fintype.card F = 4 ^ f := by
    rw [← Nat.card_eq_fintype_card, hF, ← pow_mul, mul_comm, pow_mul]
    norm_num
  by_cases hk : i.val + 1 < n / 2
  · exact isCyclic_of_le_of_equiv (rankOneShortEquiv (hσ := hσ) hk)
      (fun Q hQ => CyclicSylowGL.isCyclic_of_isPGroup_five_of_injective_GL_four_pow hf hk4
        (by norm_num) Matrix.SpecialLinearGroup.toGL Matrix.SpecialLinearGroup.toGL_injective Q
        hQ) hP h5
  · by_cases he : Even n
    · rw [eq_bot_of_isPGroup_five_rankOne_last_even hF hf he hk hP h5]
      infer_instance
    · exact isCyclic_of_le_of_equiv (rankOneLastOddEquiv hF he hk)
        (fun Q hQ => CyclicSylowGL.isCyclic_of_isPGroup_five_of_injective_GL_four_pow hf hk4
          (by norm_num) (SU (unitaryInvolution F 2 f) 3).subtype Subtype.val_injective Q hQ) hP h5

include hF in
theorem false_of_hasSubquotient_short_last (hfo : Odd f) (he : Even n) {a c : Fin (n / 2)}
    (hc : ¬ c.val + 1 < n / 2)
    (hcomm : Commutes (rankOne (rootDatum hF n).rootGroup a)
      (rankOne (rootDatum hF n).rootGroup c))
    (h : LeviSection.HasSubquotient
      (rankOne (rootDatum hF n).rootGroup a ⊔ rankOne (rootDatum hF n).rootGroup c)
      (alternatingGroup (Fin 5) × alternatingGroup (Fin 5))) : False := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  exact false_of_hasSubquotient_sup_of_commutes hcomm
    (fun P hP h5 => isCyclic_of_isPGroup_five_rankOne hF hfo a hP h5)
    (fun P hP h5 => eq_bot_of_isPGroup_five_rankOne_last_even hF hfo he hc hP h5) h

include hF in
theorem rankOne_le_blkSub {t : ℕ} (hn : n = 2 * t) {k : Fin (n / 2)} (hk : k.val + 1 < n / 2)
    (ht : k.val + 1 < t) :
    rankOne (rootDatum hF n).rootGroup k ≤ blkSub (σ := unitaryInvolution F 2 f) (blk2 t) :=
  fun g hg => by
    have hb := (isBlk_short_of_mem (hσ := unitaryInvolution_involutive hF) hk hg).1
    refine isBlk_mono hb fun a b hab hne => ?_
    have h1 := blk2_eq_blkShort hk hn ht hne
    have h2 := blk2_eq_blkShort hk hn ht (hab ▸ hne)
    exact ⟨by rw [h1, h2, hab], by rw [h1]; exact hne⟩

include hF in
theorem false_of_hasSubquotient_zero_one (hfo : Odd f) (hn6 : n = 6) {a b : Fin (n / 2)}
    (ha : a.val = 0) (hb : b.val = 1)
    (h : LeviSection.HasSubquotient
      (rankOne (rootDatum hF n).rootGroup a ⊔ rankOne (rootDatum hF n).rootGroup b)
      (alternatingGroup (Fin 5) × alternatingGroup (Fin 5))) : False := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have := Fintype.ofFinite F
  have hk4 : Fintype.card F = 4 ^ f := by
    rw [← Nat.card_eq_fintype_card, hF, ← pow_mul, mul_comm, pow_mul]
    norm_num
  have ht : n = 2 * 3 := by omega
  have hle : rankOne (rootDatum hF n).rootGroup a ⊔ rankOne (rootDatum hF n).rootGroup b ≤
      blkSub (σ := unitaryInvolution F 2 f) (blk2 3) :=
    sup_le (rankOne_le_blkSub hF ht (by omega) (by omega))
      (rankOne_le_blkSub hF ht (by omega) (by omega))
  refine LeviSection.HasSubquotient.false_of_isCyclic (p := 5) (fun P hP h5 => ?_)
    (h.mono hle) LeviSection.exists_not_isCyclic_five
  have hc := CyclicSylowGL.isCyclic_of_isPGroup_five_of_injective_GL_four_pow hfo hk4
    (by norm_num : 3 ≤ 3) (resGL (σ := unitaryInvolution F 2 f) (n := n) 3 (by omega))
    (resGL_injective (σ := unitaryInvolution F 2 f) (t := 3) ht) _
    (h5.comap_subtype (K := blkSub (σ := unitaryInvolution F 2 f) (blk2 3)))
  exact (Subgroup.subgroupOfEquivOfLe hP).isCyclic.mp hc

include hF in
theorem three_le_pRank_su_six {ζ : traceZero (unitaryInvolution F 2 f)} (hζ : (ζ : F) ≠ 0)
    {Y : Type} [Group Y] [Finite Y] {π : SU (unitaryInvolution F 2 f) n →* Y} {M : ℕ}
    (hb : BorelQuotient (rootDatum hF n) (levelWeyl (unitaryInvolution_involutive hF) ζ)
      (levelTorus (unitaryInvolution F 2 f)) π M) {J : Subgroup Y}
    (hBJ : borel (rootDatum hF n) (levelTorus (unitaryInvolution F 2 f)) ≤ J.comap π)
    (hfo : Odd f) (hn6 : n = 6) {a b c : Fin (n / 2)} (hav : a.val = 0) (hbv : b.val = 1)
    (hcv : c.val = 2) (hbI : b ∈ negIndices (rootDatum hF n) (J.comap π))
    (hcI : c ∈ negIndices (rootDatum hF n) (J.comap π))
    {X : Type} [Group X] [Finite X] (ρ : X →* Y) (hρ : Function.Surjective ρ)
    (hρker : ρ.ker ≤ Subgroup.center X) : 3 ≤ CFSG.Open.pRank 3 (J.comap ρ) := by
  have hσ := unitaryInvolution_involutive hF
  have he : Even n := ⟨3, by omega⟩
  have hD : (rootDatum hF n).divisible = ∅ := by
    show divisible n = ∅
    unfold divisible
    rw [ite_eq_left he]
  have hcb : c ≠ b := fun h => by rw [h] at hcv; omega
  obtain ⟨hcartan1, hcartan2⟩ := cartan_last_two hF he (b := b) (c := c) (by omega) (by omega)
  set k := levelWeyl hσ ζ b with hk
  have hkL : k ∈ rankOne (rootDatum hF n).rootGroup b := levelWeyl_mem_rankOne hσ ζ b
  have hkJ : π k ∈ J := rankOne_le_of_mem_negIndices hBJ hbI hkL
  have hcommk : Commutes (rankOne (rootDatum hF n).rootGroup c)
      ((rankOne (rootDatum hF n).rootGroup c).map (MulAut.conj k).toMonoidHom) :=
    commutes_rankOne_bTwo hb.ct hb.extras hD hcb hcartan1 hcartan2
  have Rc := realThreeOver_rankOne hBJ hcI (hasRealOrderThree_su hF c)
  by_cases hk3 : 3 ∣ Nat.card ρ.ker
  · exact three_le_pRank_of_pair (fun z hz => hb.ker_central z hz) ρ hρ hρker hk3 hcommk Rc
      (Rc.conj hkJ)
  · have hρ3 : Nat.Coprime 3 (Nat.card ρ.ker) :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hk3
    obtain ⟨ω, hω3, hω1⟩ := exists_order_three hF
    have hσω : unitaryInvolution F 2 f (ω : F) = ((ω⁻¹ : Fˣ) : F) :=
      unitaryInvolution_eq_inv_of_pow_three hω3 hfo
    have ha1 : a.val + 1 < n / 2 := by omega
    have hb1 : b.val + 1 < n / 2 := by omega
    obtain ⟨h, hhH, hhm, hh3, hh1⟩ :=
      exists_levelTorus_order_three hF a ω hω3 hω1 (fun hh => absurd ha1 hh)
    have haL : h ∈ rankOne (rootDatum hF n).rootGroup a :=
      levelTorus_le_rankOne hσ hζ (exists_norm_eq_of_fixed' hF) a hhH
    have hhJ : π h ∈ J := hBJ (le_sup_left (a := ⨆ i, levelTorus (unitaryInvolution F 2 f) i)
      (le_iSup (levelTorus (unitaryInvolution F 2 f)) a hhH))
    obtain ⟨g, hgΛ, hgJ, hg3, hgc, w, hwL, hwg⟩ := Rc
    have hgL : g ∈ rankOne (rootDatum hF n).rootGroup c := Subgroup.commutator_le_self _ hgΛ
    have hg1 : g ≠ 1 := fun h1 => hgc (by rw [h1]; exact Subgroup.one_mem _)
    have C1 : ∀ t ∈ rankOne (rootDatum hF n).rootGroup c,
        ∀ s ∈ rankOne (rootDatum hF n).rootGroup c, k⁻¹ * t * k * s = s * (k⁻¹ * t * k) := by
      intro t ht s hs
      have h1 := hcommk t ht (k * s * k⁻¹) ⟨s, hs, rfl⟩
      calc k⁻¹ * t * k * s = k⁻¹ * (t * (k * s * k⁻¹)) * k := by group
        _ = k⁻¹ * (k * s * k⁻¹ * t) * k := by rw [h1]
        _ = s * (k⁻¹ * t * k) := by group
    have C2 : ∀ t ∈ rankOne (rootDatum hF n).rootGroup c, h * t = t * h := fun t ht =>
      commutes_rankOne_of_cartan_eq_zero hb.extras (fun h' => by rw [h'] at hav; omega)
        (cartan_eq_zero_of_two_le hF (by omega)) h haL t ht
    have C3 : ∀ t ∈ rankOne (rootDatum hF n).rootGroup c,
        h * (k⁻¹ * t * k) = k⁻¹ * t * k * h := by
      intro t ht
      have hconj := coe_conj_diagonal (coe_levelWeyl hσ hζ b) hhm
      rw [levelPerm_symm] at hconj
      have hab1 : (⟨a.val + 1, ha1⟩ : Fin (n / 2)) = b := Fin.ext (by simp [hav, hbv])
      have hbc1 : (⟨b.val + 1, hb1⟩ : Fin (n / 2)) = c := Fin.ext (by simp [hbv, hcv])
      have hd : tFun (unitaryInvolution F 2 f) a (ω : F) (levelPerm b (lowIdx c)) =
          tFun (unitaryInvolution F 2 f) a (ω : F) (levelPerm b (Fin.rev (lowIdx c))) := by
        rw [levelPerm_rev, ← hbc1, levelPerm_lowIdx_succ hb1, ← hab1, tFun_succ_idx ha1,
          tFun_rev_succ_idx ha1, hσω, Units.val_inv_eq_inv_val]
      have hcomm' := commute_of_diag_eq_last hσ he (c := c) (by omega)
        (d := fun r => tFun (unitaryInvolution F 2 f) a (ω : F) (levelPerm b r)) hd
        (x := k * h * k⁻¹) hconj ht
      calc h * (k⁻¹ * t * k) = k⁻¹ * ((k * h * k⁻¹) * t) * k := by group
        _ = k⁻¹ * (t * (k * h * k⁻¹)) * k := by rw [hcomm']
        _ = k⁻¹ * t * k * h := by group
    set g' := k⁻¹ * g * k with hg'
    set w' := k⁻¹ * w * k with hw'
    have hg'3 : g' ^ 3 = 1 := by
      rw [hg', show k⁻¹ * g * k = k⁻¹ * g * k⁻¹⁻¹ by rw [inv_inv], conj_pow, hg3]
      group
    have hg'1 : g' ≠ 1 := fun h1 => hg1 (by
      calc g = k * (k⁻¹ * g * k) * k⁻¹ := by group
        _ = 1 := by rw [← hg', h1]; group)
    have hw'g' : w' * g' * w'⁻¹ = g'⁻¹ := by
      calc w' * g' * w'⁻¹ = k⁻¹ * (w * g * w⁻¹) * k := by rw [hg', hw']; group
        _ = g'⁻¹ := by rw [hwg, hg']; group
    have hgg' : Commute g g' := (C1 g hgL g hgL).symm
    have hgh : Commute g h := (C2 g hgL).symm
    have hg'h : Commute g' h := (C3 g hgL).symm
    have hg'J : π g' ∈ J := by
      rw [hg', map_mul, map_mul, map_inv]
      exact J.mul_mem (J.mul_mem (J.inv_mem hkJ) hgJ) hkJ
    refine (three_le_pRank_of_indep (π := π) (J := J) hgg' hgh hg'h hg3 hg'3 hh3 hgJ hg'J hhJ
      (fun p q r hmem => ?_)).trans (pRank_le_pRank_comap_of_coprime hρ hρ3 J)
    have hz : g ^ p * g' ^ q * h ^ r ∈ Subgroup.center (SU (unitaryInvolution F 2 f) n) :=
      hb.ker_central _ hmem
    have hzc : ∀ u, u * (g ^ p * g' ^ q * h ^ r) * u⁻¹ = g ^ p * g' ^ q * h ^ r := fun u => by
      rw [Subgroup.mem_center_iff.mp hz u]
      group
    have hp : 3 ∣ p := by
      have cwg' : Commute w g' := (C1 g hgL w hwL).symm
      have cwh : Commute w h := (C2 w hwL).symm
      have e1 : w * g' ^ q * w⁻¹ = g' ^ q := (cwg'.pow_right q).mul_inv_cancel
      have e2 : w * h ^ r * w⁻¹ = h ^ r := (cwh.pow_right r).mul_inv_cancel
      have h1 := hzc w
      rw [show w * (g ^ p * g' ^ q * h ^ r) * w⁻¹ =
        (w * g ^ p * w⁻¹) * (w * g' ^ q * w⁻¹) * (w * h ^ r * w⁻¹) by group, e1, e2] at h1
      exact three_dvd_of_conj_eq_inv hg3 hg1 hwg (mul_right_cancel (mul_right_cancel h1))
    have hq : 3 ∣ q := by
      have cw'g : Commute w' g := C1 w hwL g hgL
      have cw'h : Commute w' h := (C3 w hwL).symm
      have e1 : w' * g ^ p * w'⁻¹ = g ^ p := (cw'g.pow_right p).mul_inv_cancel
      have e2 : w' * h ^ r * w'⁻¹ = h ^ r := (cw'h.pow_right r).mul_inv_cancel
      have h1 := hzc w'
      rw [show w' * (g ^ p * g' ^ q * h ^ r) * w'⁻¹ =
        (w' * g ^ p * w'⁻¹) * (w' * g' ^ q * w'⁻¹) * (w' * h ^ r * w'⁻¹) by group, e1, e2] at h1
      exact three_dvd_of_conj_eq_inv hg'3 hg'1 hw'g' (mul_left_cancel (mul_right_cancel h1))
    refine ⟨hp, hq, ?_⟩
    obtain ⟨p', rfl⟩ := hp
    obtain ⟨q', rfl⟩ := hq
    have h1 := hzc (levelWeyl hσ ζ a)
    rw [pow_mul, pow_mul, hg3, hg'3, one_pow, one_pow, one_mul, one_mul] at h1
    exact three_dvd_of_conj_eq_inv hh3 hh1 (levelWeyl_conj_short_torus hσ hζ ha1 hhm) h1

end SU

section Main

open CFSG.LieType.Universal CFSG.LieType.Universal.Unitary CFSG.LieType.Universal.Unitary.SUExtras
  CFSG.LieType.CurtisTits CFSG.LieType.RootSystem CFSG.LieType.Steinberg CFSG.AGLEmbedding
  CFSG.AGLEmbedding.ParabHub CFSG.AGLEmbedding.ParabPrime CFSG.AGLEmbeddingD2.ParabLevi
  CFSG.AGLEmbeddingD2.ParabRankEngine CFSG.AGLEmbeddingD2.SquareGeneric CFSG.LieType.BorelTits
  Matrix

theorem three_le_pRank_su {n f : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2]
    (hF : Nat.card F = (2 ^ f) ^ 2) (hn : 3 ≤ n) {Y : Type} [Group Y] [Finite Y]
    (e : Y ≃* StatedProj (StatedSU n (2 ^ f) F)) {X : Type} [Group X] [Finite X]
    (ρ : X →* Y) (hρ : Function.Surjective ρ) (hρker : ρ.ker ≤ Subgroup.center X)
    (h3 : 3 ∣ Nat.card ρ.ker → 3 ∣ n ∧ 3 ∣ 2 ^ f + 1) (T : Sylow 2 Y) (J : Subgroup Y)
    (hNJ : Subgroup.normalizer ((T : Subgroup Y) : Set Y) ≤ J) (hJ : J ≠ ⊤)
    (hQ : LeviSection.HasSubquotient J (alternatingGroup (Fin 5) × alternatingGroup (Fin 5))) :
    3 ≤ CFSG.Open.pRank 3 (J.comap ρ) := by
  classical
  have := Fintype.ofFinite F
  have hσ := unitaryInvolution_involutive hF
  obtain ⟨ζ, hζ⟩ := exists_traceZero_ne_zero hF
  have hb := borelQuotient_su hF (by omega) ζ hζ e
  obtain ⟨π', hb', hker', hBJ⟩ := BorelQuotient.exists_conj_parab hb T hNJ
  have hM := hasSubquotient_leviM_of_parab hb' hBJ hQ
  have hBJ' : (borel (rootDatum hF n) (levelTorus (unitaryInvolution F 2 f))).map π' ≤ J :=
    Subgroup.map_le_iff_le_comap.mpr hBJ
  obtain ⟨j, hj⟩ := LieOut.exists_node_not_mem_negIndices hb' hBJ' hJ
  obtain ⟨ω, hω3, hω1⟩ := exists_order_three hF
  have hρ3_of : (¬ 3 ∣ n ∨ ¬ 3 ∣ 2 ^ f + 1) → Nat.Coprime 3 (Nat.card ρ.ker) := fun h =>
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 fun hd => by
      obtain ⟨h1, h2⟩ := h3 hd
      rcases h with h | h <;> contradiction
  have hπ3_of : (¬ 3 ∣ n ∨ ¬ 3 ∣ 2 ^ f + 1) → Nat.Coprime 3 (Nat.card π'.ker) := fun h => by
    rw [hker']
    exact coprime_three_card_ker hF (by omega) e h
  have hcomm : ∀ a b : Fin (n / 2), a.val + 2 ≤ b.val →
      Commutes (rankOne (rootDatum hF n).rootGroup a) (rankOne (rootDatum hF n).rootGroup b) :=
    fun a b h => commutes_rankOne_of_cartan_eq_zero hb'.extras
      (fun h' => by rw [h'] at h; omega) (cartan_eq_zero_of_two_le hF h)
  have hsub : n / 2 ≤ 2 → (negIndices (rootDatum hF n) (J.comap π')).Subsingleton := by
    intro hm2 x hx y hy
    have hxj : x.val ≠ j.val := fun h => hj (Fin.ext h ▸ hx)
    have hyj : y.val ≠ j.val := fun h => hj (Fin.ext h ▸ hy)
    have h1 : x.val < n / 2 := x.isLt
    have h2 : y.val < n / 2 := y.isLt
    have h3 : j.val < n / 2 := j.isLt
    exact Fin.ext (by omega)
  rcases Nat.even_or_odd f with hfe | hfo
  ·
    have hmod : 2 ^ f % 3 = 1 := two_pow_mod_three_of_even hfe
    have hre : ¬ 3 ∣ 2 ^ f + 1 := by omega
    have hρ3 := hρ3_of (Or.inr hre)
    have hπ3 := hπ3_of (Or.inr hre)
    have hσω : unitaryInvolution F 2 f (ω : F) = ω :=
      unitaryInvolution_eq_self_of_pow_three hω3 hfe
    by_cases hm3 : 3 ≤ n / 2
    · let a : Fin (n / 2) := ⟨0, by omega⟩
      let b : Fin (n / 2) := ⟨1, by omega⟩
      let c : Fin (n / 2) := ⟨2, by omega⟩
      obtain ⟨x, hxH, -, hx3, hx1⟩ :=
        exists_levelTorus_order_three hF a ω hω3 hω1 (fun _ _ => hσω)
      obtain ⟨y, hyH, -, hy3, hy1⟩ :=
        exists_levelTorus_order_three hF b ω hω3 hω1 (fun _ _ => hσω)
      obtain ⟨z, hzH, -, hz3, hz1⟩ :=
        exists_levelTorus_order_three hF c ω hω3 hω1 (fun _ _ => hσω)
      exact (three_le_pRank_of_torus hb'.extras hπ3 hBJ (a := a) (b := b) (c := c)
        (fun h => absurd (congrArg Fin.val h) (by simp [a, b]))
        (fun h => absurd (congrArg Fin.val h) (by simp [a, c]))
        (fun h => absurd (congrArg Fin.val h) (by simp [b, c])) hxH hyH hzH hx3 hy3 hz3 hx1 hy1
        hz1).trans (pRank_le_pRank_comap_of_coprime hρ hρ3 J)
    · exfalso
      rcases (hsub (by omega)).eq_empty_or_singleton with hI | ⟨i, hI⟩
      · rw [hI, leviM_empty] at hM
        exact false_of_hasSubquotient_bot hM
      · rw [hI, leviM_singleton] at hM
        exact false_of_hasSubquotient_of_isCyclic (fun P hP h3P =>
          isCyclic_of_isPGroup_three_rankOne hF hfe i hP h3P) hM
  ·
    have hmod : 2 ^ f % 3 = 2 := two_pow_mod_three_of_odd hfo
    have hq3 : 3 ∣ 2 ^ f + 1 := by omega
    have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
    have hone : ∀ i : Fin (rootDatum hF n).rank,
        negIndices (rootDatum hF n) (J.comap π') ⊆ {i} → False := fun i hi =>
      LeviSection.HasSubquotient.false_of_isCyclic (p := 5)
        (fun P hP h5 => isCyclic_of_isPGroup_five_rankOne hF hfo i hP h5)
        (hM.mono ((leviM_mono hi).trans (leviM_singleton (D := rootDatum hF n) i).le))
        LeviSection.exists_not_isCyclic_five
    have hπJ : ∀ (a : Fin (n / 2)) (x : SU (unitaryInvolution F 2 f) n),
        x ∈ levelTorus (unitaryInvolution F 2 f) a → π' x ∈ J := fun a x hx =>
      hBJ (le_sup_left (a := ⨆ k, levelTorus (unitaryInvolution F 2 f) k)
        (le_iSup (levelTorus (unitaryInvolution F 2 f)) a hx))
    by_cases hn7 : 7 ≤ n
    · by_cases h3n : 3 ∣ n
      · by_cases hne : Even n
        ·
          have hn12 : 12 ≤ n := by obtain ⟨r, hr⟩ := hne; omega
          let a : Fin (n / 2) := ⟨0, by omega⟩
          let b : Fin (n / 2) := ⟨2, by omega⟩
          let c : Fin (n / 2) := ⟨4, by omega⟩
          exact three_le_pRank_of_triple (fun z hz => hb'.ker_central z hz) ρ hρ hρker
            (hcomm a b (by simp [a, b])) (hcomm a c (by simp [a, c])) (hcomm b c (by simp [b, c]))
            (realThreeOver_torus_su hF hBJ (a := a) (by simp [a]; omega) hω3 hω1)
            (realThreeOver_torus_su hF hBJ (a := b) (by simp [b]; omega) hω3 hω1)
            (realThreeOver_torus_su hF hBJ (a := c) (by simp [c]; omega) hω3 hω1)
        ·
          have hn9 : 9 ≤ n := by obtain ⟨r, hr⟩ := Nat.not_even_iff_odd.1 hne; omega
          have hm4 : 4 ≤ n / 2 := by omega
          let a : Fin (n / 2) := ⟨0, by omega⟩
          let b : Fin (n / 2) := ⟨1, by omega⟩
          let c : Fin (n / 2) := ⟨2, by omega⟩
          by_cases hk : 3 ∣ Nat.card ρ.ker
          · exact three_le_pRank_of_pair (fun z hz => hb'.ker_central z hz) ρ hρ hρker hk
              (hcomm a c (by simp [a, c]))
              (realThreeOver_torus_su hF hBJ (a := a) (by simp [a]; omega) hω3 hω1)
              (realThreeOver_torus_su hF hBJ (a := c) (by simp [c]; omega) hω3 hω1)
          · have hρ3 : Nat.Coprime 3 (Nat.card ρ.ker) :=
              (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hk
            have hω : orderOf ω = 3 := orderOf_eq_prime hω3 hω1
            obtain ⟨x, hxH, hxm, hx3, hx1⟩ := exists_levelTorus_order_three hF a ω hω3 hω1
              (fun h => absurd (by simp [a]; omega) h)
            obtain ⟨y, hyH, hym, hy3, hy1⟩ := exists_levelTorus_order_three hF b ω hω3 hω1
              (fun h => absurd (by simp [b]; omega) h)
            obtain ⟨z, hzH, hzm, hz3, hz1⟩ := exists_levelTorus_order_three hF c ω hω3 hω1
              (fun h => absurd (by simp [c]; omega) h)
            refine (three_le_pRank_of_indep (π := π') (J := J)
              (hb'.extras.torus_commute a b x hxH y hyH) (hb'.extras.torus_commute a c x hxH z hzH)
              (hb'.extras.torus_commute b c y hyH z hzH) hx3 hy3 hz3 (hπJ a x hxH) (hπJ b y hyH)
              (hπJ c z hzH) (fun p q r hmem => ?_)).trans
              (pRank_le_pRank_comap_of_coprime hρ hρ3 J)
            exact torus_triple_dvd_of_central hσ hζ (a := a) (b := b) (c := c) rfl rfl rfl
              (by omega) hω hxm hym hzm (hb'.ker_central _ hmem)
      ·
        have hρ3 := hρ3_of (Or.inl h3n)
        have hπ3 := hπ3_of (Or.inl h3n)
        have hm3 : 3 ≤ n / 2 := by omega
        let a : Fin (n / 2) := ⟨0, by omega⟩
        let b : Fin (n / 2) := ⟨1, by omega⟩
        let c : Fin (n / 2) := ⟨2, by omega⟩
        obtain ⟨x, hxH, -, hx3, hx1⟩ :=
          exists_levelTorus_order_three hF a ω hω3 hω1 (fun h => absurd (by simp [a]; omega) h)
        obtain ⟨y, hyH, -, hy3, hy1⟩ :=
          exists_levelTorus_order_three hF b ω hω3 hω1 (fun h => absurd (by simp [b]; omega) h)
        obtain ⟨z, hzH, -, hz3, hz1⟩ := exists_levelTorus_order_three hF c ω hω3 hω1
          (fun h he => by
            exfalso
            obtain ⟨r, hr⟩ := he
            simp only [c] at h
            omega)
        exact (three_le_pRank_of_torus hb'.extras hπ3 hBJ (a := a) (b := b) (c := c)
          (fun h => absurd (congrArg Fin.val h) (by simp [a, b]))
          (fun h => absurd (congrArg Fin.val h) (by simp [a, c]))
          (fun h => absurd (congrArg Fin.val h) (by simp [b, c])) hxH hyH hzH hx3 hy3 hz3 hx1 hy1
          hz1).trans (pRank_le_pRank_comap_of_coprime hρ hρ3 J)
    ·
      by_cases hn6 : n = 6
      · have hm : n / 2 = 3 := by omega
        have he : Even n := ⟨3, by omega⟩
        have hj3 : j.val < 3 := by
          have h1 : j.val < n / 2 := j.isLt
          omega
        have hIne : ∀ i ∈ negIndices (rootDatum hF n) (J.comap π'), i.val ≠ j.val :=
          fun i hi h => hj (Fin.ext h ▸ hi)
        rcases (by omega : j.val = 0 ∨ j.val = 1 ∨ j.val = 2) with hj0 | hj1 | hj2
        ·
          let n0 : Fin (rootDatum hF n).rank := ⟨0, by show 0 < n / 2; omega⟩
          let n1 : Fin (rootDatum hF n).rank := ⟨1, by show 1 < n / 2; omega⟩
          let n2 : Fin (rootDatum hF n).rank := ⟨2, by show 2 < n / 2; omega⟩
          by_cases h1 : n1 ∈ negIndices (rootDatum hF n) (J.comap π')
          · by_cases h2 : n2 ∈ negIndices (rootDatum hF n) (J.comap π')
            · exact three_le_pRank_su_six hF hζ hb' hBJ hfo hn6 (a := n0) (b := n1) (c := n2)
                rfl rfl rfl h1 h2 ρ hρ hρker
            · exact (hone n1 fun i hi => by
                have h3 := hIne i hi
                have h4 : i.val < n / 2 := i.isLt
                have h5 : i ≠ n2 := fun h => h2 (h ▸ hi)
                have h6 : i.val ≠ 2 := fun h => h5 (Fin.ext h)
                exact Fin.ext (by simp only [n1]; omega)).elim
          · exact (hone n2 fun i hi => by
              have h3 := hIne i hi
              have h4 : i.val < n / 2 := i.isLt
              have h5 : i ≠ n1 := fun h => h1 (h ▸ hi)
              have h6 : i.val ≠ 1 := fun h => h5 (Fin.ext h)
              exact Fin.ext (by simp only [n2]; omega)).elim
        ·
          let n0 : Fin (rootDatum hF n).rank := ⟨0, by show 0 < n / 2; omega⟩
          let n2 : Fin (rootDatum hF n).rank := ⟨2, by show 2 < n / 2; omega⟩
          have hle : leviM (rootDatum hF n) (negIndices (rootDatum hF n) (J.comap π')) ≤
              rankOne (rootDatum hF n).rootGroup n0 ⊔ rankOne (rootDatum hF n).rootGroup n2 := by
            rw [← leviM_pair]
            refine leviM_mono fun i hi => ?_
            have h1 := hIne i hi
            have h2 : i.val < n / 2 := i.isLt
            have : i.val = 0 ∨ i.val = 2 := by omega
            rcases this with h | h
            · exact Or.inl (Fin.ext h)
            · exact Or.inr (Fin.ext h)
          exact (false_of_hasSubquotient_short_last hF hfo he (by simp [n2]; omega)
            (hcomm n0 n2 (by simp [n0, n2])) (hM.mono hle)).elim
        ·
          let n0 : Fin (rootDatum hF n).rank := ⟨0, by show 0 < n / 2; omega⟩
          let n1 : Fin (rootDatum hF n).rank := ⟨1, by show 1 < n / 2; omega⟩
          have hle : leviM (rootDatum hF n) (negIndices (rootDatum hF n) (J.comap π')) ≤
              rankOne (rootDatum hF n).rootGroup n0 ⊔ rankOne (rootDatum hF n).rootGroup n1 := by
            rw [← leviM_pair]
            refine leviM_mono fun i hi => ?_
            have h1 := hIne i hi
            have h2 : i.val < n / 2 := i.isLt
            have : i.val = 0 ∨ i.val = 1 := by omega
            rcases this with h | h
            · exact Or.inl (Fin.ext h)
            · exact Or.inr (Fin.ext h)
          exact (false_of_hasSubquotient_zero_one hF hfo hn6 (a := n0) (b := n1) rfl rfl
            (hM.mono hle)).elim
      · exfalso
        rcases (hsub (by omega)).eq_empty_or_singleton with hI | ⟨i, hI⟩
        · rw [hI, leviM_empty] at hM
          exact false_of_hasSubquotient_bot hM
        · exact hone i hI.le

end Main

end CFSG.AGLEmbeddingD2.SquareUnitary
