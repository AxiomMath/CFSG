module

public import CFSG.RankThree.PartOne.KC.OrthogonalFixedBlock
public import CFSG.ClassicalGroups.Orthogonal.Hyperbolic

public section

namespace CFSG.LieType.SeitzGeneration.OrthBlk

open Module QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.PartOne.KCOrthogonal

section Avg

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

@[expose] noncomputable def normOp (g : V ≃ₗ[K] V) (p : ℕ) : V →ₗ[K] V :=
  ∑ i ∈ Finset.range p, ((g ^ i : V ≃ₗ[K] V) : V →ₗ[K] V)

theorem normOp_apply (g : V ≃ₗ[K] V) (p : ℕ) (v : V) :
    normOp g p v = ∑ i ∈ Finset.range p, (g ^ i) v := by
  simp [normOp, LinearMap.sum_apply]

theorem apply_normOp {g : V ≃ₗ[K] V} {p : ℕ} (hg : g ^ p = 1) (v : V) :
    g (normOp g p v) = normOp g p v := by
  rw [normOp_apply, map_sum]
  have h3 : ∀ i : ℕ, g ((g ^ i) v) = (g ^ (i + 1)) v := fun i => by
    rw [pow_succ', LinearEquiv.mul_apply]
  simp only [h3]
  have h1 := Finset.sum_range_succ' (fun i => (g ^ i) v) p
  have h2 := Finset.sum_range_succ (fun i => (g ^ i) v) p
  have hp : (g ^ p) v = v := by rw [hg]; rfl
  simp only [pow_zero] at h1
  rw [hp] at h2
  have h0 : (1 : V ≃ₗ[K] V) v = v := rfl
  rw [h0] at h1
  exact add_right_cancel (h1.symm.trans h2)

theorem pow_apply_of_fixed {g : V ≃ₗ[K] V} {v : V} (hv : g v = v) (i : ℕ) : (g ^ i) v = v := by
  induction i with
  | zero => rfl
  | succ i ih => rw [pow_succ', LinearEquiv.mul_apply, ih, hv]

theorem normOp_apply_of_fixed {g : V ≃ₗ[K] V} {p : ℕ} {v : V} (hv : g v = v) :
    normOp g p v = (p : K) • v := by
  rw [normOp_apply]
  simp [pow_apply_of_fixed hv, Finset.card_range, Nat.cast_smul_eq_nsmul]

theorem normOp_normOp {g : V ≃ₗ[K] V} {p : ℕ} (hg : g ^ p = 1) (v : V) :
    normOp g p (normOp g p v) = (p : K) • normOp g p v :=
  normOp_apply_of_fixed (apply_normOp hg v)

theorem normOp_sub_inv {g : V ≃ₗ[K] V} {p : ℕ} (hg : g ^ p = 1) (hpK : (p : K) ≠ 0) (v : V) :
    normOp g p (v - (p : K)⁻¹ • normOp g p v) = 0 := by
  rw [map_sub, map_smul, normOp_normOp hg, smul_smul, inv_mul_cancel₀ hpK, one_smul, sub_self]

theorem pow_apply_mem {g : V ≃ₗ[K] V} {S : Submodule K V} (hS : ∀ s ∈ S, g s ∈ S) (i : ℕ) :
    ∀ s ∈ S, (g ^ i) s ∈ S := by
  induction i with
  | zero => intro s hs; exact hs
  | succ i ih => intro s hs; rw [pow_succ', LinearEquiv.mul_apply]; exact hS _ (ih s hs)

theorem normOp_mem {g : V ≃ₗ[K] V} {p : ℕ} {S : Submodule K V} (hS : ∀ s ∈ S, g s ∈ S) {s : V}
    (hs : s ∈ S) : normOp g p s ∈ S := by
  rw [normOp_apply]
  exact S.sum_mem fun i _ => pow_apply_mem hS i s hs

end Avg

section Split

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
  {g : V ≃ₗ[K] V} {p : ℕ}

@[expose] def fixIn (g : V ≃ₗ[K] V) (S : Submodule K V) : Submodule K V :=
  S ⊓ LinearMap.ker ((g : V →ₗ[K] V) - 1)

@[expose] noncomputable def normKer (g : V ≃ₗ[K] V) (p : ℕ) (S : Submodule K V) : Submodule K V :=
  S ⊓ LinearMap.ker (normOp g p)

theorem mem_fixIn {S : Submodule K V} {v : V} : v ∈ fixIn g S ↔ v ∈ S ∧ g v = v := by
  simp [fixIn, LinearMap.mem_ker, sub_eq_zero]

theorem mem_normKer {S : Submodule K V} {v : V} :
    v ∈ normKer g p S ↔ v ∈ S ∧ normOp g p v = 0 := by
  simp [normKer, LinearMap.mem_ker]

theorem exists_add_fixIn_normKer (hg : g ^ p = 1) (hpK : (p : K) ≠ 0) {S : Submodule K V}
    (hS : ∀ s ∈ S, g s ∈ S) {s : V} (hs : s ∈ S) :
    ∃ c ∈ fixIn g S, ∃ b ∈ normKer g p S, c + b = s := by
  refine ⟨(p : K)⁻¹ • normOp g p s, ?_, s - (p : K)⁻¹ • normOp g p s, ?_, add_sub_cancel _ _⟩
  · exact mem_fixIn.mpr ⟨S.smul_mem _ (normOp_mem hS hs), by rw [map_smul, apply_normOp hg]⟩
  · exact mem_normKer.mpr ⟨S.sub_mem hs (S.smul_mem _ (normOp_mem hS hs)),
      normOp_sub_inv hg hpK s⟩

theorem sup_fixIn_normKer (hg : g ^ p = 1) (hpK : (p : K) ≠ 0) {S : Submodule K V}
    (hS : ∀ s ∈ S, g s ∈ S) : fixIn g S ⊔ normKer g p S = S := by
  refine le_antisymm (sup_le inf_le_left inf_le_left) fun s hs => ?_
  obtain ⟨c, hc, b, hb, rfl⟩ := exists_add_fixIn_normKer hg hpK hS hs
  exact Submodule.add_mem_sup hc hb

theorem disjoint_fixIn_normKer (hpK : (p : K) ≠ 0) (S : Submodule K V) :
    Disjoint (fixIn g S) (normKer g p S) := by
  rw [Submodule.disjoint_def]
  intro v hv hv'
  have h1 := (mem_fixIn.mp hv).2
  have h2 := (mem_normKer.mp hv').2
  rw [normOp_apply_of_fixed h1] at h2
  exact (smul_eq_zero.mp h2).resolve_left hpK

theorem polar_fixIn_normKer (hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hpK : (p : K) ≠ 0)
    {u w : V} (hu : g u = u) (hw : normOp g p w = 0) : polar Q u w = 0 := by
  have h1 : polar Q u (normOp g p w) = ∑ i ∈ Finset.range p, polar Q u ((g ^ i) w) := by
    rw [normOp_apply, ← polarBilin_apply_apply, map_sum]
    simp only [polarBilin_apply_apply]
  have h2 : ∀ i ∈ Finset.range p, polar Q u ((g ^ i) w) = polar Q u w := fun i _ => by
    have hi : g ^ i ∈ TauCeti.QuadraticMap.orthogonalGroup Q := pow_mem hgO i
    have := TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hi u w
    rw [pow_apply_of_fixed hu i] at this
    exact this
  rw [hw, polar_zero_right, Finset.sum_congr rfl h2, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul] at h1
  exact (mul_eq_zero.mp h1.symm).resolve_left hpK

theorem polarNondegOn_fixIn (hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hg : g ^ p = 1)
    (hpK : (p : K) ≠ 0) {S : Submodule K V} (hS : PolarNondegOn Q S) (hst : ∀ s ∈ S, g s ∈ S) :
    PolarNondegOn Q (fixIn g S) := by
  intro x hx hxy
  refine hS x (mem_fixIn.mp hx).1 fun y hy => ?_
  obtain ⟨c, hc, b, hb, rfl⟩ := exists_add_fixIn_normKer hg hpK hst hy
  rw [polar_add_right, hxy c hc, polar_fixIn_normKer hgO hpK (mem_fixIn.mp hx).2
    (mem_normKer.mp hb).2, add_zero]

theorem polarNondegOn_normKer (hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hg : g ^ p = 1)
    (hpK : (p : K) ≠ 0) {S : Submodule K V} (hS : PolarNondegOn Q S) (hst : ∀ s ∈ S, g s ∈ S) :
    PolarNondegOn Q (normKer g p S) := by
  intro x hx hxy
  refine hS x (mem_normKer.mp hx).1 fun y hy => ?_
  obtain ⟨c, hc, b, hb, rfl⟩ := exists_add_fixIn_normKer hg hpK hst hy
  rw [polar_add_right, hxy b hb, polar_comm Q x c, polar_fixIn_normKer hgO hpK
    (mem_fixIn.mp hc).2 (mem_normKer.mp hx).2, zero_add]

theorem fixIn_stable {a b : V ≃ₗ[K] V} (hab : Commute a b) {S : Submodule K V}
    (hSb : ∀ s ∈ S, b s ∈ S) : ∀ v ∈ fixIn a S, b v ∈ fixIn a S := by
  intro v hv
  obtain ⟨hvS, hva⟩ := mem_fixIn.mp hv
  refine mem_fixIn.mpr ⟨hSb v hvS, ?_⟩
  have : (a * b) v = (b * a) v := by rw [hab.eq]
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hva] at this
  exact this

theorem normOp_comm {a b : V ≃ₗ[K] V} (hab : Commute a b) (p : ℕ) (v : V) :
    normOp a p (b v) = b (normOp a p v) := by
  rw [normOp_apply, normOp_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have : (a ^ i * b) v = (b * a ^ i) v := by rw [(hab.pow_left i).eq]
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply] at this
  exact this

theorem normKer_stable {a b : V ≃ₗ[K] V} (hab : Commute a b) {S : Submodule K V}
    (hSb : ∀ s ∈ S, b s ∈ S) : ∀ v ∈ normKer a p S, b v ∈ normKer a p S := by
  intro v hv
  obtain ⟨hvS, hva⟩ := mem_normKer.mp hv
  refine mem_normKer.mpr ⟨hSb v hvS, ?_⟩
  rw [normOp_comm hab, hva, map_zero]

end Split

section Key

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {p : ℕ}

theorem sum_range_mul_eq {M : Type*} [AddCommMonoid M] (hp : p.Prime) (f : ℕ → M)
    (hf : ∀ k, f k = f (k % p)) {m : ℕ} (hm : ¬ p ∣ m) :
    ∑ j ∈ Finset.range p, f (j * m) = ∑ k ∈ Finset.range p, f k := by
  have hcop : Nat.Coprime p m := (Nat.Prime.coprime_iff_not_dvd hp).mpr hm
  obtain ⟨m', -, hm'⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop.symm hp.one_lt
  refine Finset.sum_nbij (fun j => j * m % p) ?_ ?_ ?_ (fun j _ => hf (j * m))
  · intro j _
    exact Finset.mem_range.mpr (Nat.mod_lt _ hp.pos)
  · intro j₁ h₁ j₂ h₂ h
    have h₁' : j₁ < p := Finset.mem_range.mp h₁
    have h₂' : j₂ < p := Finset.mem_range.mp h₂
    have h3 : j₁ * m ≡ j₂ * m [MOD p] := h
    have h4 := Nat.ModEq.cancel_right_of_coprime hcop h3
    have h5 : j₁ % p = j₂ % p := h4
    rwa [Nat.mod_eq_of_lt h₁', Nat.mod_eq_of_lt h₂'] at h5
  · intro k hk
    have hk' : k < p := Finset.mem_range.mp hk
    refine ⟨k * m' % p, Finset.mem_range.mpr (Nat.mod_lt _ hp.pos), ?_⟩
    have h1 : m * m' ≡ 1 [MOD p] := by
      show m * m' % p = 1 % p
      rw [hm', Nat.mod_eq_of_lt hp.one_lt]
    have h2 : (k * m' % p) * m ≡ k [MOD p] := by
      calc (k * m' % p) * m ≡ (k * m') * m [MOD p] := (Nat.mod_modEq _ _).mul_right m
        _ = k * (m * m') := by ring
        _ ≡ k * 1 [MOD p] := h1.mul_left k
        _ = k := mul_one k
    show (k * m' % p) * m % p = k
    rw [h2, Nat.mod_eq_of_lt hk']

theorem norm_identity (hp : p.Prime) {a b : V ≃ₗ[K] V} (hab : Commute a b) (hb : b ^ p = 1)
    (v : V) :
    ∑ j ∈ Finset.range p, normOp (a * b ^ j) p v + normOp b p v =
      p • v + normOp a p (normOp b p v) := by
  have hpow : ∀ j i : ℕ, (a * b ^ j) ^ i = a ^ i * b ^ (j * i) := fun j i => by
    rw [(hab.pow_right j).mul_pow, ← pow_mul]
  obtain ⟨p', hp'⟩ : ∃ p', p = p' + 1 := Nat.exists_eq_succ_of_ne_zero hp.ne_zero
  have e1 : ∑ j ∈ Finset.range p, normOp (a * b ^ j) p v =
      ∑ i ∈ Finset.range p, ∑ j ∈ Finset.range p, (a ^ i) ((b ^ (j * i)) v) := by
    simp only [normOp_apply, hpow, LinearEquiv.mul_apply]
    exact Finset.sum_comm
  have e2 : normOp a p (normOp b p v) =
      ∑ i ∈ Finset.range p, ∑ k ∈ Finset.range p, (a ^ i) ((b ^ k) v) := by
    simp only [normOp_apply, map_sum]
    exact Finset.sum_comm
  rw [e1, e2, normOp_apply b p v]
  have hsplit : ∀ G : ℕ → V, ∑ i ∈ Finset.range p, G i = ∑ i ∈ Finset.range p', G (i + 1) + G 0 :=
    fun G => by rw [hp', Finset.sum_range_succ']
  rw [hsplit (fun i => ∑ j ∈ Finset.range p, (a ^ i) ((b ^ (j * i)) v)),
    hsplit (fun i => ∑ k ∈ Finset.range p, (a ^ i) ((b ^ k) v))]
  have hmid : ∀ i ∈ Finset.range p', ∑ j ∈ Finset.range p, (a ^ (i + 1)) ((b ^ (j * (i + 1))) v) =
      ∑ k ∈ Finset.range p, (a ^ (i + 1)) ((b ^ k) v) := by
    intro i hi
    have hi' : i < p' := Finset.mem_range.mp hi
    refine sum_range_mul_eq (f := fun k => (a ^ (i + 1)) ((b ^ k) v)) hp ?_ ?_
    · intro k
      show (a ^ (i + 1)) ((b ^ k) v) = (a ^ (i + 1)) ((b ^ (k % p)) v)
      rw [← pow_eq_pow_mod k hb]
    · intro hd
      have := Nat.le_of_dvd (Nat.succ_pos i) hd
      omega
  rw [Finset.sum_congr rfl hmid]
  have h0 : ∑ j ∈ Finset.range p, (a ^ 0) ((b ^ (j * 0)) v) = p • v := by
    simp [Finset.card_range]
  rw [h0]
  simp only [pow_zero]
  have h0' : ∀ k : ℕ, (1 : V ≃ₗ[K] V) ((b ^ k) v) = (b ^ k) v := fun k => rfl
  simp only [h0']
  abel

theorem eq_zero_of_fixedPointFree_plane (hp : p.Prime) (hpK : (p : K) ≠ 0) {a b : V ≃ₗ[K] V}
    (hab : Commute a b) (ha : a ^ p = 1) (hb : b ^ p = 1) {S : Submodule K V}
    (hSa : ∀ s ∈ S, a s ∈ S) (hSb : ∀ s ∈ S, b s ∈ S)
    (h : ∀ i j : ℕ, ¬ (p ∣ i ∧ p ∣ j) → ∀ s ∈ S, (a ^ i * b ^ j) s = s → s = 0) :
    ∀ v ∈ S, v = 0 := by
  intro v hv
  have hnorm : ∀ g : V ≃ₗ[K] V, g ^ p = 1 → (∀ s ∈ S, g s ∈ S) →
      (∀ s ∈ S, g s = s → s = 0) → ∀ s ∈ S, normOp g p s = 0 := by
    intro g hg hgS hgf s hs
    exact hgf _ (normOp_mem hgS hs) (apply_normOp hg s)
  have hb0 : normOp b p v = 0 := by
    refine hnorm b hb hSb (fun s hs hfix => h 0 1 (fun hd => ?_) s hs (by simpa using hfix)) v hv
    exact absurd (Nat.le_of_dvd one_pos hd.2) (by have := hp.one_lt; omega)
  have hnormj : ∀ j ∈ Finset.range p, normOp (a * b ^ j) p v = 0 := by
    intro j _
    have hcomm : Commute a (b ^ j) := hab.pow_right j
    have hg : (a * b ^ j) ^ p = 1 := by
      rw [hcomm.mul_pow, ha, ← pow_mul, mul_comm, pow_mul, hb, one_pow, one_mul]
    have hgS : ∀ s ∈ S, (a * b ^ j) s ∈ S := fun s hs => by
      rw [LinearEquiv.mul_apply]
      exact hSa _ (pow_apply_mem hSb j s hs)
    refine hnorm _ hg hgS (fun s hs hfix => h 1 j (fun hd => ?_) s hs (by simpa using hfix)) v hv
    exact absurd (Nat.le_of_dvd one_pos hd.1) (by have := hp.one_lt; omega)
  have := norm_identity hp hab hb v
  rw [Finset.sum_eq_zero hnormj, hb0, map_zero] at this
  have h2 : (p : K) • v = 0 := by rw [Nat.cast_smul_eq_nsmul]; simpa using this.symm
  exact (smul_eq_zero.mp h2).resolve_left hpK

end Key

section Block

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V} {p : ℕ}

@[expose] def stabPW (S : Submodule K V) : Subgroup (V ≃ₗ[K] V) where
  carrier := {g | ∀ s ∈ S, g s = s}
  mul_mem' := fun {a b} ha hb s hs => by rw [LinearEquiv.mul_apply, hb s hs, ha s hs]
  one_mem' := fun _ _ => rfl
  inv_mem' := fun {a} ha s hs => (LinearEquiv.symm_apply_eq a).mpr (ha s hs).symm

theorem mem_stabPW {S : Submodule K V} {g : V ≃ₗ[K] V} : g ∈ stabPW S ↔ ∀ s ∈ S, g s = s :=
  Iff.rfl

theorem stabPW_sup (C B : Submodule K V) : stabPW (C ⊔ B) = stabPW C ⊓ stabPW B := by
  ext g
  refine ⟨fun h => ⟨fun s hs => h s (Submodule.mem_sup_left hs),
    fun s hs => h s (Submodule.mem_sup_right hs)⟩, fun ⟨hC, hB⟩ s hs => ?_⟩
  obtain ⟨c, hc, b, hb, rfl⟩ := Submodule.mem_sup.mp hs
  rw [map_add, hC c hc, hB b hb]

theorem stabPW_top : stabPW (⊤ : Submodule K V) = ⊥ := by
  ext g
  refine ⟨fun h => ?_, fun h => ?_⟩
  · exact Subgroup.mem_bot.mpr (LinearEquiv.ext fun v => h v Submodule.mem_top)
  · rw [Subgroup.mem_bot.mp h]
    exact fun _ _ => rfl

variable (Q) in
abbrev perp (S : Submodule K V) : Submodule K V :=
  LinearMap.BilinForm.orthogonal (polarBilin Q) S

theorem mem_perp {S : Submodule K V} {v : V} : v ∈ perp Q S ↔ ∀ s ∈ S, polar Q s v = 0 := by
  rw [perp, LinearMap.BilinForm.mem_orthogonal_iff]
  simp [polarBilin_apply_apply]

theorem isCompl_perp [FiniteDimensional K V] {S : Submodule K V} (hS : PolarNondegOn Q S) :
    IsCompl S (perp Q S) := by
  rw [perp, LinearMap.BilinForm.isCompl_orthogonal_iff_disjoint
    (QuadraticMap.isSymm_polarBilin Q).isRefl, Submodule.disjoint_def]
  intro x hxS hxp
  refine hS x hxS fun y hy => ?_
  rw [polar_comm]
  exact mem_perp.mp hxp y hy

theorem polarNondegOn_perp [FiniteDimensional K V] (hQ : (polarBilin Q).Nondegenerate)
    {S : Submodule K V} (hS : PolarNondegOn Q S) : PolarNondegOn Q (perp Q S) := by
  intro x hx hxy
  refine eq_zero_of_polar_eq_zero hQ fun v => ?_
  obtain ⟨s, hs, t, ht, rfl⟩ := Submodule.mem_sup.mp ((isCompl_perp hS).sup_eq_top ▸
    Submodule.mem_top (x := v))
  rw [polar_add_right, hxy t ht, polar_comm Q x s, mem_perp.mp hx s hs, add_zero]

@[expose] noncomputable def extendId [FiniteDimensional K V] {S : Submodule K V}
    (hS : PolarNondegOn Q S) (a : V ≃ₗ[K] V) (h1 : ∀ s ∈ S, a s ∈ S)
    (h2 : ∀ s ∈ S, a.symm s ∈ S) : V ≃ₗ[K] V :=
  glue (isCompl_perp hS) (restrictEquiv S a h1 h2) 1

theorem extendId_apply [FiniteDimensional K V] {S : Submodule K V} (hS : PolarNondegOn Q S)
    {a : V ≃ₗ[K] V} (h1 : ∀ s ∈ S, a s ∈ S) (h2 : ∀ s ∈ S, a.symm s ∈ S) {u r : V}
    (hu : u ∈ S) (hr : r ∈ perp Q S) : extendId hS a h1 h2 (u + r) = a u + r :=
  glue_apply (isCompl_perp hS) (restrictEquiv S a h1 h2) 1 ⟨u, hu⟩ ⟨r, hr⟩

theorem extendId_pow [FiniteDimensional K V] {S : Submodule K V} (hS : PolarNondegOn Q S)
    {a : V ≃ₗ[K] V} (h1 : ∀ s ∈ S, a s ∈ S) (h2 : ∀ s ∈ S, a.symm s ∈ S) {u r : V}
    (hu : u ∈ S) (hr : r ∈ perp Q S) (n : ℕ) :
    (extendId hS a h1 h2 ^ n) (u + r) = (a ^ n) u + r := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', LinearEquiv.mul_apply, ih,
      extendId_apply hS h1 h2 (pow_apply_mem h1 n u hu) hr, pow_succ', LinearEquiv.mul_apply]

structure IsBlock (Q : QuadraticForm K V) (p : ℕ) (S : Submodule K V) (g : V ≃ₗ[K] V) : Prop where
  mem : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q
  pow : g ^ p = 1
  ne : g ≠ 1
  fix : ∀ v : V, (∀ s ∈ S, polar Q s v = 0) → g v = v

theorem extendId_isBlock [FiniteDimensional K V] {S : Submodule K V} (hS : PolarNondegOn Q S)
    {a : V ≃ₗ[K] V} (hO : a ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (ha : a ^ p = 1)
    (h1 : ∀ s ∈ S, a s ∈ S) (h2 : ∀ s ∈ S, a.symm s ∈ S) (hmove : ∃ s ∈ S, a s ≠ s) :
    IsBlock Q p S (extendId hS a h1 h2) := by
  have hdec : ∀ v : V, ∃ u ∈ S, ∃ r ∈ perp Q S, u + r = v := fun v => by
    obtain ⟨u, hu, r, hr, h⟩ := Submodule.mem_sup.mp ((isCompl_perp hS).sup_eq_top ▸
      Submodule.mem_top (x := v))
    exact ⟨u, hu, r, hr, h⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
    intro v
    obtain ⟨u, hu, r, hr, rfl⟩ := hdec v
    rw [extendId_apply hS h1 h2 hu hr, QuadraticMap.map_add (⇑Q) (a u) r,
      QuadraticMap.map_add (⇑Q) u r, mem_perp.mp hr (a u) (h1 u hu), mem_perp.mp hr u hu,
      TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hO u]
  · refine LinearEquiv.ext fun v => ?_
    obtain ⟨u, hu, r, hr, rfl⟩ := hdec v
    rw [extendId_pow hS h1 h2 hu hr p, ha]
    rfl
  · obtain ⟨s, hs, hsa⟩ := hmove
    intro h
    apply hsa
    have := extendId_apply hS h1 h2 hs (zero_mem (perp Q S))
    rw [h, add_zero, add_zero] at this
    exact this.symm
  · intro v hv
    have := extendId_apply hS h1 h2 (zero_mem S) (mem_perp.mpr fun s hs => hv s hs)
    rw [zero_add, map_zero, zero_add] at this
    exact this

end Block

end CFSG.LieType.SeitzGeneration.OrthBlk
