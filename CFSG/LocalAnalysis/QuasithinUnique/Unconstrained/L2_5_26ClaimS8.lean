module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_26ClaimPerm
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_26ClaimTheta
public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamilies

public section

namespace CFSG.QuasithinUnique.Claim2526

open Equiv CFSG.QuasithinUnique.A6Facts CFSG.Open

variable {G : Type*} [Group G]

structure S8Data (L : Subgroup G) (φ : ↥L ≃* alternatingGroup (Fin 8)) (t i : G) : Prop where
  t_sq : t * t = 1
  i_sq : i * i = 1
  t_i : t * i = i * t
  i_ne : i ≠ 1
  t_mem : t ∈ Subgroup.normalizer (L : Set G)
  i_cent : ∀ k ∈ L, i * k = k * i
  hind : ∀ y y' : ↥L, (y' : G) = t⁻¹ * y * t →
    φ y' = (MulAut.conjNormal (Equiv.swap 0 1) : MulAut (alternatingGroup (Fin 8))) (φ y)

section Group

variable {L : Subgroup G} {φ : ↥L ≃* alternatingGroup (Fin 8)} {t i : G}

theorem S8Data.i_mem_normalizer (D : S8Data L φ t i) : i ∈ Subgroup.normalizer (L : Set G) := by
  apply Subgroup.centralizer_le_normalizer
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  exact (D.i_cent k hk).symm

theorem V0set_mul (D : S8Data L φ t i) {a b : G} (ha : a = 1 ∨ a = t ∨ a = i ∨ a = t * i)
    (hb : b = 1 ∨ b = t ∨ b = i ∨ b = t * i) :
    a * b = 1 ∨ a * b = t ∨ a * b = i ∨ a * b = t * i := by
  have ht := D.t_sq
  have hi := D.i_sq
  have hti := D.t_i
  have hit : i * t = t * i := hti.symm
  rcases ha with ha | ha | ha | ha <;> rcases hb with hb | hb | hb | hb <;> rw [ha, hb]
  · left; simp
  · right; left; simp
  · right; right; left; simp
  · right; right; right; simp
  · right; left; simp
  · left; exact ht
  · right; right; right; rfl
  · right; right; left
    calc t * (t * i) = (t * t) * i := by rw [mul_assoc]
      _ = i := by rw [ht, one_mul]
  · right; right; left; simp
  · right; right; right; exact hit
  · left; exact hi
  · right; left
    calc i * (t * i) = (i * t) * i := by rw [mul_assoc]
      _ = (t * i) * i := by rw [hit]
      _ = t * (i * i) := by rw [mul_assoc]
      _ = t := by rw [hi, mul_one]
  · right; right; right; simp
  · right; right; left
    calc t * i * t = t * (i * t) := by rw [mul_assoc]
      _ = t * (t * i) := by rw [hit]
      _ = (t * t) * i := by rw [mul_assoc]
      _ = i := by rw [ht, one_mul]
  · right; left
    calc t * i * i = t * (i * i) := by rw [mul_assoc]
      _ = t := by rw [hi, mul_one]
  · left
    calc t * i * (t * i) = t * (i * t) * i := by group
      _ = t * (t * i) * i := by rw [hit]
      _ = (t * t) * (i * i) := by group
      _ = 1 := by rw [ht, hi, one_mul]

theorem V0set_sq (D : S8Data L φ t i) {v : G} (hv : v = 1 ∨ v = t ∨ v = i ∨ v = t * i) :
    v * v = 1 := by
  have ht := D.t_sq
  have hi := D.i_sq
  have hit : i * t = t * i := D.t_i.symm
  rcases hv with hv | hv | hv | hv <;> rw [hv]
  · simp
  · exact ht
  · exact hi
  · calc t * i * (t * i) = t * (i * t) * i := by group
      _ = t * (t * i) * i := by rw [hit]
      _ = (t * t) * (i * i) := by group
      _ = 1 := by rw [ht, hi, one_mul]

theorem V0set_inv (D : S8Data L φ t i) {v : G} (hv : v = 1 ∨ v = t ∨ v = i ∨ v = t * i) :
    v⁻¹ = v := inv_eq_of_mul_eq_one_right (V0set_sq D hv)

theorem V0set_mem_normalizer (D : S8Data L φ t i) {v : G}
    (hv : v = 1 ∨ v = t ∨ v = i ∨ v = t * i) : v ∈ Subgroup.normalizer (L : Set G) := by
  rcases hv with hv | hv | hv | hv <;> rw [hv]
  · exact Subgroup.one_mem _
  · exact D.t_mem
  · exact D.i_mem_normalizer
  · exact Subgroup.mul_mem _ D.t_mem D.i_mem_normalizer

theorem V0set_conj (D : S8Data L φ t i) {v : G} (hv : v = 1 ∨ v = t ∨ v = i ∨ v = t * i)
    {k : G} (hk : k ∈ L) : v * k * v⁻¹ ∈ L := by
  have hvN := V0set_mem_normalizer D hv
  exact (Subgroup.mem_normalizer_iff.mp hvN k).mp hk

@[expose] def H0 (D : S8Data L φ t i) : Subgroup G where
  carrier := {g | ∃ k ∈ L, ∃ v, (v = 1 ∨ v = t ∨ v = i ∨ v = t * i) ∧ g = k * v}
  mul_mem' := by
    rintro a b ⟨k, hk, v, hv, rfl⟩ ⟨k', hk', v', hv', rfl⟩
    refine ⟨k * (v * k' * v⁻¹), L.mul_mem hk (V0set_conj D hv hk'), v * v', V0set_mul D hv hv', ?_⟩
    group
  one_mem' := ⟨1, L.one_mem, 1, Or.inl rfl, by simp⟩
  inv_mem' := by
    rintro a ⟨k, hk, v, hv, rfl⟩
    refine ⟨v * k⁻¹ * v⁻¹, V0set_conj D hv (L.inv_mem hk), v, hv, ?_⟩
    have := V0set_inv D hv
    calc (k * v)⁻¹ = v⁻¹ * k⁻¹ := mul_inv_rev k v
      _ = v * k⁻¹ := by rw [this]
      _ = (v * k⁻¹ * v⁻¹) * v := by group

theorem L_le_H0 (D : S8Data L φ t i) : L ≤ H0 D := fun k hk =>
  ⟨k, hk, 1, Or.inl rfl, by simp⟩

theorem i_mem_H0 (D : S8Data L φ t i) : i ∈ H0 D :=
  ⟨1, L.one_mem, i, Or.inr (Or.inr (Or.inl rfl)), by simp⟩

theorem H0_le_normalizer (D : S8Data L φ t i) : H0 D ≤ Subgroup.normalizer (L : Set G) := by
  rintro g ⟨k, hk, v, hv, rfl⟩
  exact Subgroup.mul_mem _ (Subgroup.le_normalizer hk) (V0set_mem_normalizer D hv)

open scoped Classical in
@[expose] noncomputable def thetaFun (L : Subgroup G) (φ : ↥L ≃* alternatingGroup (Fin 8)) (g : G) :
    Equiv.Perm (Fin 8) :=
  if h : g ∈ Subgroup.normalizer (L : Set G) then thetaHom L φ ⟨g, h⟩ else 1

theorem thetaFun_of_mem {g : G} (h : g ∈ Subgroup.normalizer (L : Set G)) :
    thetaFun L φ g = thetaHom L φ ⟨g, h⟩ := by simp [thetaFun, h]

theorem thetaFun_mul {g g' : G} (hg : g ∈ Subgroup.normalizer (L : Set G))
    (hg' : g' ∈ Subgroup.normalizer (L : Set G)) :
    thetaFun L φ (g * g') = thetaFun L φ g * thetaFun L φ g' := by
  rw [thetaFun_of_mem (Subgroup.mul_mem _ hg hg'), thetaFun_of_mem hg, thetaFun_of_mem hg',
    ← map_mul]
  rfl

theorem thetaFun_one : thetaFun L φ (1 : G) = 1 := by
  rw [thetaFun_of_mem (Subgroup.one_mem _)]
  have : (⟨1, Subgroup.one_mem _⟩ : ↥(Subgroup.normalizer (L : Set G))) = 1 := rfl
  rw [this, map_one]

theorem thetaFun_inv {g : G} (hg : g ∈ Subgroup.normalizer (L : Set G)) :
    thetaFun L φ g⁻¹ = (thetaFun L φ g)⁻¹ := by
  rw [thetaFun_of_mem (Subgroup.inv_mem _ hg), thetaFun_of_mem hg, ← map_inv]
  rfl

theorem thetaFun_of_mem_L {k : G} (hk : k ∈ L) :
    thetaFun L φ k = (φ ⟨k, hk⟩ : Equiv.Perm (Fin 8)) := by
  rw [thetaFun_of_mem (Subgroup.le_normalizer hk)]
  exact theta_apply_of_mem L φ ⟨k, hk⟩

theorem thetaFun_t (D : S8Data L φ t i) : thetaFun L φ t = Equiv.swap 0 1 := by
  rw [thetaFun_of_mem D.t_mem]
  apply theta_swap L φ ⟨t, D.t_mem⟩ D.t_sq
  exact D.hind

theorem thetaFun_i (D : S8Data L φ t i) : thetaFun L φ i = 1 := by
  rw [thetaFun_of_mem D.i_mem_normalizer]
  rw [theta_eq_one_iff]
  intro k hk
  exact D.i_cent k hk

theorem thetaFun_V0 (D : S8Data L φ t i) : thetaFun L φ (t * i) = Equiv.swap 0 1 := by
  rw [thetaFun_mul D.t_mem D.i_mem_normalizer, thetaFun_t D, thetaFun_i D, mul_one]

theorem thetaFun_kv (D : S8Data L φ t i) {k v : G} (hk : k ∈ L)
    (hv : v = 1 ∨ v = t ∨ v = i ∨ v = t * i) :
    thetaFun L φ (k * v) = (φ ⟨k, hk⟩ : Equiv.Perm (Fin 8)) * thetaFun L φ v := by
  rw [thetaFun_mul (Subgroup.le_normalizer hk) (V0set_mem_normalizer D hv), thetaFun_of_mem_L hk]

theorem sign_swap01 : Equiv.Perm.sign (Equiv.swap (0 : Fin 8) 1) = -1 :=
  Equiv.Perm.sign_swap (by decide)

theorem swap01_not_mem_alt {σ : Equiv.Perm (Fin 8)} (hσ : σ ∈ alternatingGroup (Fin 8)) :
    σ * Equiv.swap 0 1 ≠ 1 := by
  intro h
  have h1 := Equiv.Perm.mem_alternatingGroup.mp hσ
  have h2 : σ = (Equiv.swap 0 1)⁻¹ := eq_inv_of_mul_eq_one_left h
  rw [h2, map_inv, sign_swap01] at h1
  exact absurd h1 (by decide)

theorem theta_ker (D : S8Data L φ t i) {g : G} (hg : g ∈ H0 D) (h1 : thetaFun L φ g = 1) :
    g = 1 ∨ g = i := by
  obtain ⟨k, hk, v, hv, rfl⟩ := hg
  rw [thetaFun_kv D hk hv] at h1
  have hφ : ((φ ⟨k, hk⟩ : alternatingGroup (Fin 8)) : Equiv.Perm (Fin 8)) ∈ alternatingGroup (Fin 8) :=
    (φ ⟨k, hk⟩).2
  have hk1 : k = 1 → True := fun _ => trivial
  rcases hv with hv | hv | hv | hv
  · rw [hv, thetaFun_one, mul_one] at h1
    have h2 : φ ⟨k, hk⟩ = 1 := Subtype.ext h1
    have h3 : (⟨k, hk⟩ : ↥L) = 1 := by rw [← φ.map_one] at h2; exact φ.injective h2
    have h4 : k = 1 := congrArg Subtype.val h3
    left; rw [hv, h4]; simp
  · exfalso
    rw [hv, thetaFun_t D] at h1
    exact swap01_not_mem_alt hφ h1
  · rw [hv, thetaFun_i D, mul_one] at h1
    have h2 : φ ⟨k, hk⟩ = 1 := Subtype.ext h1
    have h3 : (⟨k, hk⟩ : ↥L) = 1 := by rw [← φ.map_one] at h2; exact φ.injective h2
    have h4 : k = 1 := congrArg Subtype.val h3
    right; rw [hv, h4]; simp
  · exfalso
    rw [hv, thetaFun_V0 D] at h1
    exact swap01_not_mem_alt hφ h1

theorem theta_surj (D : S8Data L φ t i) (σ : Equiv.Perm (Fin 8)) :
    ∃ g ∈ H0 D, thetaFun L φ g = σ := by
  by_cases hσ : σ ∈ alternatingGroup (Fin 8)
  · obtain ⟨k, hk⟩ := φ.surjective ⟨σ, hσ⟩
    refine ⟨(k : G) * 1, ⟨k, k.2, 1, Or.inl rfl, rfl⟩, ?_⟩
    rw [thetaFun_kv D k.2 (Or.inl rfl), thetaFun_one, mul_one]
    have : φ ⟨(k : G), k.2⟩ = ⟨σ, hσ⟩ := hk
    rw [this]
  · have hσ' : σ * Equiv.swap 0 1 ∈ alternatingGroup (Fin 8) := by
      rw [Equiv.Perm.mem_alternatingGroup, map_mul, sign_swap01]
      have : Equiv.Perm.sign σ = -1 := by
        rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h
        · exact absurd (Equiv.Perm.mem_alternatingGroup.mpr h) hσ
        · exact h
      rw [this]
      decide
    obtain ⟨k, hk⟩ := φ.surjective ⟨σ * Equiv.swap 0 1, hσ'⟩
    refine ⟨(k : G) * t, ⟨k, k.2, t, Or.inr (Or.inl rfl), rfl⟩, ?_⟩
    rw [thetaFun_kv D k.2 (Or.inr (Or.inl rfl)), thetaFun_t D]
    have : φ ⟨(k : G), k.2⟩ = ⟨σ * Equiv.swap 0 1, hσ'⟩ := hk
    rw [this]
    simp

theorem thetaFun_pow {g : G} (hg : g ∈ Subgroup.normalizer (L : Set G)) (m : ℕ) :
    thetaFun L φ (g ^ m) = (thetaFun L φ g) ^ m := by
  induction m with
  | zero => simp [thetaFun_one]
  | succ m ih =>
    rw [pow_succ, thetaFun_mul (Subgroup.pow_mem _ hg m) hg, ih, pow_succ]

@[expose] def Hpre (D : S8Data L φ t i) (B : Subgroup (Equiv.Perm (Fin 8))) : Subgroup G where
  carrier := {g | g ∈ H0 D ∧ thetaFun L φ g ∈ B}
  mul_mem' := by
    rintro a b ⟨ha, haB⟩ ⟨hb, hbB⟩
    refine ⟨(H0 D).mul_mem ha hb, ?_⟩
    rw [thetaFun_mul (H0_le_normalizer D ha) (H0_le_normalizer D hb)]
    exact B.mul_mem haB hbB
  one_mem' := ⟨(H0 D).one_mem, by rw [thetaFun_one]; exact B.one_mem⟩
  inv_mem' := by
    rintro a ⟨ha, haB⟩
    refine ⟨(H0 D).inv_mem ha, ?_⟩
    rw [thetaFun_inv (H0_le_normalizer D ha)]
    exact B.inv_mem haB

variable (D : S8Data L φ t i)

theorem Hpre_le_H0 (B : Subgroup (Equiv.Perm (Fin 8))) : Hpre D B ≤ H0 D := fun _ h => h.1

theorem Hpre_mono {B B' : Subgroup (Equiv.Perm (Fin 8))} (h : B ≤ B') : Hpre D B ≤ Hpre D B' :=
  fun _ hg => ⟨hg.1, h hg.2⟩

theorem i_mem_Hpre (B : Subgroup (Equiv.Perm (Fin 8))) : i ∈ Hpre D B :=
  ⟨i_mem_H0 D, by rw [thetaFun_i D]; exact B.one_mem⟩

theorem card_Hpre (B : Subgroup (Equiv.Perm (Fin 8))) : Nat.card (Hpre D B) = 2 * Nat.card B := by
  let f : ↥(Hpre D B) →* ↥B :=
    { toFun := fun g => ⟨thetaFun L φ g, g.2.2⟩
      map_one' := by
        apply Subtype.ext
        show thetaFun L φ ((1 : ↥(Hpre D B)) : G) = 1
        exact thetaFun_one
      map_mul' := fun a b => by
        apply Subtype.ext
        show thetaFun L φ ((a * b : ↥(Hpre D B)) : G) = thetaFun L φ (a : G) * thetaFun L φ (b : G)
        exact thetaFun_mul (H0_le_normalizer D a.2.1) (H0_le_normalizer D b.2.1) }
  have hsurj : Function.Surjective f := by
    intro σ
    obtain ⟨g, hg, hgσ⟩ := theta_surj D σ
    refine ⟨⟨g, hg, by rw [hgσ]; exact σ.2⟩, ?_⟩
    apply Subtype.ext
    exact hgσ
  have hker : Nat.card f.ker = 2 := by
    rw [Nat.card_eq_two_iff' (1 : f.ker)]
    let y : f.ker := ⟨⟨i, i_mem_H0 D, by rw [thetaFun_i D]; exact B.one_mem⟩, by
      rw [MonoidHom.mem_ker]
      apply Subtype.ext
      show thetaFun L φ i = 1
      exact thetaFun_i D⟩
    refine ⟨y, ?_, ?_⟩
    · intro h
      have := congrArg (fun z : f.ker => ((z : ↥(Hpre D B)) : G)) h
      exact D.i_ne this
    · intro z hz
      have hz1 : thetaFun L φ ((z : ↥(Hpre D B)) : G) = 1 :=
        congrArg Subtype.val (MonoidHom.mem_ker.mp z.2)
      rcases theta_ker D z.1.2.1 hz1 with h | h
      · exfalso
        apply hz
        apply Subtype.ext
        apply Subtype.ext
        exact h
      · apply Subtype.ext
        apply Subtype.ext
        exact h
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hsurj).toEquiv, hker] at h1
  rw [h1, mul_comm]

theorem pow_two_pow_of_theta {g : G} (hg : g ∈ H0 D) {n : ℕ} (h : (thetaFun L φ g) ^ (2 ^ n) = 1) :
    g ^ (2 ^ (n + 1)) = 1 := by
  have h1 : thetaFun L φ (g ^ (2 ^ n)) = 1 := by
    rw [thetaFun_pow (H0_le_normalizer D hg), h]
  have h2 : g ^ (2 ^ n) ∈ H0 D := Subgroup.pow_mem _ hg _
  have h3 := theta_ker D h2 h1
  rw [pow_succ, pow_mul]
  rcases h3 with h3 | h3
  · rw [h3]; simp
  · rw [h3, sq]; exact D.i_sq

theorem isPGroup_Hpre {B : Subgroup (Equiv.Perm (Fin 8))} (hB : IsPGroup 2 B) :
    IsPGroup 2 (Hpre D B) := by
  intro g
  obtain ⟨n, hn⟩ := hB ⟨thetaFun L φ (g : G), g.2.2⟩
  refine ⟨n + 1, ?_⟩
  apply Subtype.ext
  show (g : G) ^ (2 ^ (n + 1)) = 1
  apply pow_two_pow_of_theta D g.2.1
  exact congrArg Subtype.val hn

variable [Finite G]

theorem charTwo_Hpre {B Q : Subgroup (Equiv.Perm (Fin 8))} (hQB : Q ≤ B)
    (hQn : ∀ σ ∈ B, ∀ q ∈ Q, σ * q * σ⁻¹ ∈ Q) (hQsq : ∀ q ∈ Q, q * q = 1)
    (hcent : ∀ σ ∈ B, (∀ q ∈ Q, σ * q = q * σ) → σ ∈ Q) : CharTwo (Hpre D B) := by
  have hQtB : Hpre D Q ≤ Hpre D B := Hpre_mono D hQB
  have hnorm : Hpre D B ≤ Subgroup.normalizer ((Hpre D Q : Subgroup G) : Set G) := by
    intro g hg
    apply mem_normalizer_of_forall_conj
    intro q hq
    have hgH := hg.1
    have hqH := hq.1
    refine ⟨(H0 D).mul_mem ((H0 D).mul_mem hgH hqH) ((H0 D).inv_mem hgH), ?_⟩
    rw [thetaFun_mul (H0_le_normalizer D ((H0 D).mul_mem hgH hqH)) (H0_le_normalizer D ((H0 D).inv_mem hgH)),
      thetaFun_mul (H0_le_normalizer D hgH) (H0_le_normalizer D hqH),
      thetaFun_inv (H0_le_normalizer D hgH)]
    exact hQn _ hg.2 _ hq.2
  have hpg : IsPGroup 2 (Hpre D Q) := by
    intro q
    refine ⟨2, ?_⟩
    apply Subtype.ext
    show ((q : ↥(Hpre D Q)) : G) ^ (2 ^ 2) = 1
    have hq := q.2
    have h1 : thetaFun L φ (q : G) * thetaFun L φ (q : G) = 1 := hQsq _ hq.2
    have h2 : (thetaFun L φ (q : G)) ^ (2 ^ 1) = 1 := by rw [pow_one, sq]; exact h1
    exact pow_two_pow_of_theta D hq.1 h2
  have hle : Hpre D Q ≤ pCoreOf 2 (Hpre D B) := le_pCoreOf_of_normalizes hQtB hnorm hpg
  intro g hg
  obtain ⟨hgB, hgC⟩ := hg
  have hgC' : ∀ q ∈ Hpre D Q, g * q = q * g := by
    intro q hq
    have := Subgroup.mem_centralizer_iff.mp hgC q (hle hq)
    exact this.symm
  have hΘ : thetaFun L φ g ∈ Q := by
    apply hcent _ hgB.2
    intro q' hq'
    obtain ⟨q, hqH, hqθ⟩ := theta_surj D q'
    have hqQ : q ∈ Hpre D Q := ⟨hqH, by rw [hqθ]; exact hq'⟩
    have := hgC' q hqQ
    have h2 := congrArg (thetaFun L φ) this
    rw [thetaFun_mul (H0_le_normalizer D hgB.1) (H0_le_normalizer D hqH),
      thetaFun_mul (H0_le_normalizer D hqH) (H0_le_normalizer D hgB.1), hqθ] at h2
    exact h2
  exact hle ⟨hgB.1, hΘ⟩

omit [Finite G] in
theorem isSylowTwoOf_Hpre_P8 {B : Subgroup (Equiv.Perm (Fin 8))} (hB : P8 ≤ B) :
    IsSylowTwoOf (Hpre D P8) (Hpre D B) := by
  refine ⟨Hpre_mono D hB, isPGroup_Hpre D isPGroup_P8, ?_⟩
  have hc1 := card_Hpre D P8
  have hc2 := card_Hpre D B
  rw [card_P8] at hc1
  have hdvd : Nat.card B ∣ 40320 := card_perm_fin8 ▸ Subgroup.card_subgroup_dvd_card B
  have h128 : 128 ∣ Nat.card B := card_P8 ▸ Subgroup.card_dvd_of_le hB
  obtain ⟨m, hm⟩ := h128
  have hm315 : m ∣ 315 := by
    have h1 : 128 * m ∣ 128 * 315 := by
      rw [← hm]
      simpa using hdvd
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) h1
  have hidx := Subgroup.card_mul_index ((Hpre D P8).subgroupOf (Hpre D B))
  have hcardsub : Nat.card ((Hpre D P8).subgroupOf (Hpre D B)) = 256 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Hpre_mono D hB)).toEquiv]
    exact hc1
  rw [hcardsub, hc2, hm] at hidx
  have hi : ((Hpre D P8).subgroupOf (Hpre D B)).index = m := by omega
  rw [hi]
  intro h2
  have := Nat.dvd_trans h2 hm315
  norm_num at this

theorem i_mem_pCore (B : Subgroup (Equiv.Perm (Fin 8))) : i ∈ pCoreOf 2 (Hpre D B) := by
  have hbot : IsPGroup 2 (⊥ : Subgroup (Equiv.Perm (Fin 8))) := IsPGroup.of_card (n := 0) (by simp)
  have hpg := isPGroup_Hpre D hbot
  have hle : Hpre D ⊥ ≤ Hpre D B := Hpre_mono D bot_le
  have hnorm : Hpre D B ≤ Subgroup.normalizer ((Hpre D ⊥ : Subgroup G) : Set G) := by
    intro g hg
    apply mem_normalizer_of_forall_conj
    intro q hq
    have hgH := hg.1
    have hqH := hq.1
    refine ⟨(H0 D).mul_mem ((H0 D).mul_mem hgH hqH) ((H0 D).inv_mem hgH), ?_⟩
    have hq1 : thetaFun L φ q = 1 := Subgroup.mem_bot.mp hq.2
    rw [thetaFun_mul (H0_le_normalizer D ((H0 D).mul_mem hgH hqH)) (H0_le_normalizer D ((H0 D).inv_mem hgH)),
      thetaFun_mul (H0_le_normalizer D hgH) (H0_le_normalizer D hqH),
      thetaFun_inv (H0_le_normalizer D hgH), hq1, mul_one, mul_inv_cancel]
    exact Subgroup.one_mem _
  have h1 := le_pCoreOf_of_normalizes hle hnorm hpg
  exact h1 ⟨i_mem_H0 D, by rw [thetaFun_i D]; exact Subgroup.one_mem _⟩

theorem pCore_ne_bot (B : Subgroup (Equiv.Perm (Fin 8))) : pCoreOf 2 (Hpre D B) ≠ ⊥ := by
  intro h
  have := i_mem_pCore D B
  rw [h, Subgroup.mem_bot] at this
  exact D.i_ne this

omit [Finite G] in
theorem H0_le_of_B1_B2 {X : Subgroup G} (h1 : Hpre D B1 ≤ X) (h2 : Hpre D B2 ≤ X) : H0 D ≤ X := by
  let Y : Subgroup (Equiv.Perm (Fin 8)) :=
    { carrier := {σ | ∃ x ∈ X, x ∈ H0 D ∧ thetaFun L φ x = σ}
      mul_mem' := by
        rintro a b ⟨x, hx, hxH, rfl⟩ ⟨y, hy, hyH, rfl⟩
        exact ⟨x * y, X.mul_mem hx hy, (H0 D).mul_mem hxH hyH,
          thetaFun_mul (H0_le_normalizer D hxH) (H0_le_normalizer D hyH)⟩
      one_mem' := ⟨1, X.one_mem, (H0 D).one_mem, thetaFun_one⟩
      inv_mem' := by
        rintro a ⟨x, hx, hxH, rfl⟩
        exact ⟨x⁻¹, X.inv_mem hx, (H0 D).inv_mem hxH, thetaFun_inv (H0_le_normalizer D hxH)⟩ }
  have hB1 : B1 ≤ Y := by
    intro σ hσ
    obtain ⟨g, hg, hgσ⟩ := theta_surj D σ
    exact ⟨g, h1 ⟨hg, by rw [hgσ]; exact hσ⟩, hg, hgσ⟩
  have hB2 : B2 ≤ Y := by
    intro σ hσ
    obtain ⟨g, hg, hgσ⟩ := theta_surj D σ
    exact ⟨g, h2 ⟨hg, by rw [hgσ]; exact hσ⟩, hg, hgσ⟩
  have hY : Y = ⊤ := by
    rw [eq_top_iff, ← sup_B1_B2]
    exact sup_le hB1 hB2
  intro g hg
  have hmem : thetaFun L φ g ∈ Y := by rw [hY]; trivial
  obtain ⟨x, hx, hxH, hxθ⟩ := hmem
  have hxg : thetaFun L φ (x⁻¹ * g) = 1 := by
    rw [thetaFun_mul (H0_le_normalizer D ((H0 D).inv_mem hxH)) (H0_le_normalizer D hg),
      thetaFun_inv (H0_le_normalizer D hxH), hxθ, inv_mul_cancel]
  rcases theta_ker D ((H0 D).mul_mem ((H0 D).inv_mem hxH) hg) hxg with h | h
  · have : g = x := by
      have := h
      rw [inv_mul_eq_one] at this
      exact this.symm
    rw [this]
    exact hx
  · have : g = x * i := by rw [← h]; group
    rw [this]
    exact X.mul_mem hx (h1 (i_mem_Hpre D B1))

theorem E8_le_B1 : E8 ≤ B1 := by
  intro σ hσ
  rw [mem_B1_iff]
  refine Equiv.ext fun k => ?_
  rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
  rcases hσ k with h | h
  · rw [h]
    rcases hσ (zeta8 k) with h' | h'
    · exact h'
    · exfalso
      rw [zeta8_apply_apply] at h'
      exact zeta8_ne k (σ.injective (h'.trans h.symm))
  · rw [h, zeta8_apply_apply]
    rcases hσ (zeta8 k) with h' | h'
    · exfalso
      exact zeta8_ne k (σ.injective (h'.trans h.symm))
    · rw [h', zeta8_apply_apply]

theorem exists_two_locals :
    ∃ H1 H2 T0 : Subgroup G, H1 ≤ H0 D ∧ H2 ≤ H0 D ∧ T0 ≤ H1 ∧ T0 ≤ H2 ∧ CharTwo H1 ∧
      CharTwo H2 ∧ pCoreOf 2 H1 ≠ ⊥ ∧ pCoreOf 2 H2 ≠ ⊥ ∧ IsSylowTwoOf T0 H1 ∧
      IsSylowTwoOf T0 H2 ∧ Nat.card T0 = 256 ∧ (∀ X : Subgroup G, H1 ≤ X → H2 ≤ X → H0 D ≤ X) := by
  refine ⟨Hpre D B1, Hpre D B2, Hpre D P8, Hpre_le_H0 D _, Hpre_le_H0 D _, Hpre_mono D P8_le_B1,
    Hpre_mono D P8_le_B2, ?_, ?_, pCore_ne_bot D _, pCore_ne_bot D _,
    isSylowTwoOf_Hpre_P8 D P8_le_B1, isSylowTwoOf_Hpre_P8 D P8_le_B2, ?_,
    fun X h1 h2 => H0_le_of_B1_B2 D h1 h2⟩
  · exact charTwo_Hpre D E8_le_B1 (fun σ hσ q hq => E8_normal hσ hq) (fun q hq => E8_sq hq)
      (fun σ _ h => centralizer_E8_le (h _ swap01_mem_E8) (h _ swap23_mem_E8)
        (h _ swap45_mem_E8) (h _ swap67_mem_E8))
  · have hg : ∀ g ∈ v8Gens, g ∈ V8 := fun g hg => Subgroup.subset_closure hg
    exact charTwo_Hpre D (fun x hx => Subgroup.le_normalizer hx : V8 ≤ B2)
      (fun σ hσ q hq => (Subgroup.mem_normalizer_iff.mp hσ q).mp hq)
      (fun q hq => V8_sq hq)
      (fun σ _ h => centralizer_V8_le (h _ (hg _ (by simp [v8Gens]))) (h _ (hg _ (by simp [v8Gens])))
        (h _ (hg _ (by simp [v8Gens]))) (h _ (hg _ (by simp [v8Gens]))))
  · rw [card_Hpre D P8, card_P8]

end Group

end CFSG.QuasithinUnique.Claim2526
