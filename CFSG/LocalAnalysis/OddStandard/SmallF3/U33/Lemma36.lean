module

public import CFSG.GH74.GLS.Bg.TwoGroups.Free2

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33

open scoped commutatorElement

@[expose] def ActsRegularly {G : Type*} [Group G] (t : G) (N M : Subgroup G) : Prop :=
  ∀ x ∈ M, ⁅t, x⁆ ∈ N → ∃ u ∈ M, x * ⁅t, u⁆⁻¹ ∈ N

private lemma mul_commutator_mem_iff {G : Type*} [Group G] {N M : Subgroup G}
    (hcomm : ∀ x ∈ M, ∀ y ∈ M, ⁅x, y⁆ ∈ N) {a b : G} (ha : a ∈ M) (hb : b ∈ M) :
    a * b ∈ N ↔ b * a ∈ N := by
  constructor
  · intro h
    have hc : ⁅b⁻¹, a⁻¹⁆ ∈ N := hcomm _ (M.inv_mem hb) _ (M.inv_mem ha)
    have hba : b * a = (a * b) * ⁅b⁻¹, a⁻¹⁆ := by
      simp only [commutatorElement_def]; group
    rw [hba]; exact N.mul_mem h hc
  · intro h
    have hc : ⁅a⁻¹, b⁻¹⁆ ∈ N := hcomm _ (M.inv_mem ha) _ (M.inv_mem hb)
    have hab : a * b = (b * a) * ⁅a⁻¹, b⁻¹⁆ := by
      simp only [commutatorElement_def]; group
    rw [hab]; exact N.mul_mem h hc

private lemma card_fix_comm {G : Type*} [Group G] {t : G} {N M : Subgroup G}
    (hcomm : ∀ x ∈ M, ∀ y ∈ M, ⁅x, y⁆ ∈ N)
    (htM : ∀ g ∈ M, t * g * t⁻¹ ∈ M) :
    Nat.card {g : G // g ∈ M ∧ ⁅t, g⁆ ∈ N}
      = Nat.card {g : G // g ∈ M ∧ g⁻¹ * (t * g * t⁻¹) ∈ N} := by
  refine Nat.card_congr (Equiv.subtypeEquivRight (fun g => ?_))
  constructor
  · rintro ⟨hg, hcg⟩
    exact ⟨hg, (mul_commutator_mem_iff hcomm (htM g hg) (M.inv_mem hg)).mp
      (by simpa only [commutatorElement_def] using hcg)⟩
  · rintro ⟨hg, hcg⟩
    exact ⟨hg, by simpa only [commutatorElement_def] using
      (mul_commutator_mem_iff hcomm (htM g hg) (M.inv_mem hg)).mpr hcg⟩

section Lemma36

variable {G : Type} [Group G] [Finite G]

theorem actsRegularly_iff_card {t : G} (ht : orderOf t = 2) {N M : Subgroup G} (hNM : N ≤ M)
    (hcomm : ∀ x ∈ M, ∀ y ∈ M, ⁅x, y⁆ ∈ N) (hsq : ∀ x ∈ M, x ^ 2 ∈ N)
    (htN : ∀ g ∈ N, t * g * t⁻¹ ∈ N) (htM : ∀ g ∈ M, t * g * t⁻¹ ∈ M) :
    ActsRegularly t N M ↔
      Nat.card {g : G // g ∈ M ∧ ⁅t, g⁆ ∈ N} ^ 2 = Nat.card ↥M * Nat.card ↥N := by
  classical
  have ht2 : t * t = 1 := CFSG.GH74.GLS.Bg.TwoGroups.mul_self_eq_one_of_orderOf_eq_two ht
  have hNnorm : ∀ m ∈ M, ∀ n ∈ N, m * n * m⁻¹ ∈ N := by
    intro m hm n hn
    have h1 : m * n * m⁻¹ = ⁅m, n⁆ * n := by
      simp only [commutatorElement_def]; group
    rw [h1]
    exact N.mul_mem (hcomm m hm n (hNM hn)) hn
  let Nn : Subgroup M := N.subgroupOf M
  have hmemNn : ∀ a : M, a ∈ Nn ↔ (a : G) ∈ N := fun a => Iff.rfl
  have hnormal : Nn.Normal := ⟨by
    intro n hn g
    rw [hmemNn] at hn ⊢
    exact hNnorm g g.2 n hn⟩
  let V := M ⧸ Nn
  let ct : M →* M :=
    { toFun := fun a => ⟨t * a * t⁻¹, htM a a.2⟩
      map_one' := by apply Subtype.ext; simp
      map_mul' := by intro a b; apply Subtype.ext; simp [mul_assoc] }
  have hct : ∀ a : M, ((ct a : M) : G) = t * a * t⁻¹ := fun a => rfl
  have hctNn : Nn ≤ Nn.comap ct := by
    intro n hn
    rw [Subgroup.mem_comap, hmemNn, hct]
    exact htN n hn
  let σ : V →* V := QuotientGroup.map Nn Nn ct hctNn
  have hσmk : ∀ a : M, σ (a : V) = ((ct a : M) : V) := fun a => rfl
  have hσσ : ∀ v : V, σ (σ v) = v := by
    intro v
    induction v using QuotientGroup.induction_on with
    | _ a =>
      rw [hσmk, hσmk]
      congr 1
      apply Subtype.ext
      rw [hct, hct]
      have h1 : t * (t * (a : G) * t⁻¹) * t⁻¹ = (a : G) := by
        calc t * (t * (a : G) * t⁻¹) * t⁻¹ = (t * t) * (a : G) * (t⁻¹ * t⁻¹) := by group
          _ = (a : G) := by rw [ht2, ← mul_inv_rev, ht2]; simp
      exact h1
  have hVcomm : ∀ a b : V, a * b = b * a := by
    intro a b
    induction a using QuotientGroup.induction_on with
    | _ a =>
      induction b using QuotientGroup.induction_on with
      | _ b =>
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
        apply QuotientGroup.eq.mpr
        rw [hmemNn]
        have e : (((a * b)⁻¹ * (b * a) : M) : G) = ⁅(b : G)⁻¹, (a : G)⁻¹⁆ := by
          simp only [commutatorElement_def, Subgroup.coe_mul, InvMemClass.coe_inv]; group
        rw [e]
        exact hcomm _ (M.inv_mem b.2) _ (M.inv_mem a.2)
  have hVsq : ∀ a : V, a * a = 1 := by
    intro a
    induction a using QuotientGroup.induction_on with
    | _ a =>
      rw [← QuotientGroup.mk_mul]
      apply (QuotientGroup.eq_one_iff _).mpr
      rw [hmemNn]
      have e : (((a * a : M)) : G) = (a : G) ^ 2 := by simp [pow_two]
      rw [e]
      exact hsq a a.2
  have hfix : ∀ a : M, σ (a : V) = (a : V) ↔ ((a : G)⁻¹ * (t * (a : G) * t⁻¹)) ∈ N := by
    intro a
    rw [hσmk, eq_comm, QuotientGroup.eq, hmemNn]
    simp [hct]
  let Fx : Subgroup V := MonoidHom.eqLocus σ (MonoidHom.id V)
  have hFx : ∀ v, v ∈ Fx ↔ σ v = v := fun v => Iff.rfl
  have hδmul : ∀ a b : V, σ (a * b) * (a * b)⁻¹ = (σ a * a⁻¹) * (σ b * b⁻¹) := by
    intro a b
    rw [map_mul, mul_inv_rev]
    calc σ a * σ b * (b⁻¹ * a⁻¹) = σ a * (σ b * b⁻¹) * a⁻¹ := by group
      _ = σ a * a⁻¹ * (σ b * b⁻¹) := by
            rw [mul_assoc, hVcomm (σ b * b⁻¹) a⁻¹, ← mul_assoc]
      _ = (σ a * a⁻¹) * (σ b * b⁻¹) := by group
  let δ : V →* V := MonoidHom.mk' (fun v => σ v * v⁻¹) hδmul
  have hδ : ∀ v, δ v = σ v * v⁻¹ := fun v => rfl
  have hker : δ.ker = Fx := by
    ext v
    rw [MonoidHom.mem_ker, hδ, hFx]
    constructor
    · intro h
      have := congrArg (fun z => z * v) h
      simpa [mul_assoc] using this
    · intro h
      rw [h]; simp
  have hrange_le : δ.range ≤ Fx := by
    rintro _ ⟨v, rfl⟩
    rw [hFx, hδ, map_mul, map_inv, hσσ]
    have hv : v⁻¹ = v := inv_eq_of_mul_eq_one_right (hVsq v)
    have hsv : (σ v)⁻¹ = σ v := inv_eq_of_mul_eq_one_right (hVsq (σ v))
    rw [hv, hsv]
    exact hVcomm v (σ v)
  have hV : Nat.card Fx * Nat.card δ.range = Nat.card V := by
    have := Subgroup.card_ker_mul_card_range δ
    rwa [hker] at this
  have hAct : ActsRegularly t N M ↔ Fx ≤ δ.range := by
    constructor
    · intro hreg v hv
      obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective v
      have hfixa : (a : G)⁻¹ * (t * (a : G) * t⁻¹) ∈ N := (hfix a).mp hv
      have hca : ⁅t, (a : G)⁆ ∈ N :=
        (mul_commutator_mem_iff hcomm (htM a a.2) (M.inv_mem a.2)).mpr
          (by simpa only [commutatorElement_def] using hfixa)
      obtain ⟨u, huM, hu⟩ := hreg (a : G) a.2 hca
      refine ⟨(⟨u, huM⟩ : M), ?_⟩
      rw [hδ, hσmk, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
      apply QuotientGroup.eq.mpr
      rw [hmemNn]
      have hcoe : (((ct ⟨u, huM⟩ * ⟨u, huM⟩⁻¹ : M)) : G) = ⁅t, u⁆ := by
        rw [Subgroup.coe_mul, hct, Subgroup.coe_inv]
        simp only [commutatorElement_def]
      have hb : ⁅t, u⁆⁻¹ ∈ M :=
        M.inv_mem (M.mul_mem (htM u huM) (M.inv_mem huM))
      rw [Subgroup.coe_mul, Subgroup.coe_inv, hcoe]
      exact (mul_commutator_mem_iff hcomm a.2 hb).mp hu
    · intro hle x hxM hcx
      have hxfix : σ ((⟨x, hxM⟩ : M) : V) = ((⟨x, hxM⟩ : M) : V) :=
        (hfix ⟨x, hxM⟩).mpr
          ((mul_commutator_mem_iff hcomm (htM x hxM) (M.inv_mem hxM)).mp
            (by simpa only [commutatorElement_def] using hcx))
      obtain ⟨w, hw⟩ := hle ((hFx _).mpr hxfix)
      obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective w
      refine ⟨(u : G), u.2, ?_⟩
      have hw' := hw
      rw [hδ, hσmk, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul] at hw'
      have hmem := QuotientGroup.eq.mp hw'
      rw [hmemNn] at hmem
      have hcoe : (((ct u * u⁻¹ : M)) : G) = ⁅t, (u : G)⁆ := by
        rw [Subgroup.coe_mul, hct, Subgroup.coe_inv]
        simp only [commutatorElement_def]
      rw [Subgroup.coe_mul, Subgroup.coe_inv, hcoe] at hmem
      exact (mul_commutator_mem_iff hcomm
        (M.inv_mem (M.mul_mem (htM u u.2) (M.inv_mem u.2))) hxM).mp hmem
  have hC : Nat.card {g : G // g ∈ M ∧ ⁅t, g⁆ ∈ N} = Nat.card Fx * Nat.card ↥N := by
    have hfsurj : Function.Surjective (QuotientGroup.mk' Nn : M →* V) :=
      QuotientGroup.mk'_surjective Nn
    have hker' : (QuotientGroup.mk' Nn : M →* V).ker = Nn := QuotientGroup.ker_mk' Nn
    have hcomap := CFSG.GH74.GLS.Bg.TwoGroups.card_comap_of_surjective
      (QuotientGroup.mk' Nn : M →* V) hfsurj Fx
    rw [hker'] at hcomap
    have hNnN : Nat.card Nn = Nat.card ↥N :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNM).toEquiv
    have he : Nat.card {g : G // g ∈ M ∧ ⁅t, g⁆ ∈ N}
        = Nat.card (Fx.comap (QuotientGroup.mk' Nn)) := by
      let φ : {g : G // g ∈ M ∧ ⁅t, g⁆ ∈ N} → ↥(Fx.comap (QuotientGroup.mk' Nn)) :=
        fun p => ⟨⟨p.1, p.2.1⟩, Subgroup.mem_comap.mpr ((hFx _).mpr
          ((hfix ⟨p.1, p.2.1⟩).mpr ((mul_commutator_mem_iff hcomm (htM p.1 p.2.1)
            (M.inv_mem p.2.1)).mp (by simpa only [commutatorElement_def] using p.2.2))))⟩
      have hφ : Function.Bijective φ := by
        constructor
        · intro a b hab
          exact Subtype.ext (congrArg (fun z => (z.1 : M).1) hab)
        · intro q
          have hfixq : σ (q.1 : V) = (q.1 : V) := (hFx _).mp (Subgroup.mem_comap.mp q.2)
          refine ⟨⟨q.1, q.1.2, ?_⟩, ?_⟩
          · exact (mul_commutator_mem_iff hcomm (htM q.1 q.1.2) (M.inv_mem q.1.2)).mpr
              (by simpa only [commutatorElement_def] using (hfix q.1).mp hfixq)
          · apply Subtype.ext; exact Subtype.ext rfl
      exact Nat.card_congr (Equiv.ofBijective φ hφ)
    rw [he, hcomap, hNnN]
  have hMcard : Nat.card ↥M = Nat.card V * Nat.card ↥N := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup Nn
    have h2 : Nat.card Nn = Nat.card ↥N :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNM).toEquiv
    rw [h1, h2]
  have hkey : ActsRegularly t N M ↔ Nat.card Fx ^ 2 = Nat.card V := by
    rw [hAct]
    constructor
    · intro hle'
      have heq : Fx = δ.range := le_antisymm hle' hrange_le
      rw [← hV, heq, sq]
    · intro hsq
      have : Nat.card Fx * Nat.card Fx = Nat.card Fx * Nat.card δ.range := by
        rw [← sq, hsq, ← hV]
      have hcard : Nat.card Fx = Nat.card δ.range :=
        Nat.eq_of_mul_eq_mul_left Nat.card_pos this
      exact le_of_eq (Subgroup.eq_of_le_of_card_ge hrange_le (le_of_eq hcard)).symm
  rw [hkey, hC, hMcard]
  constructor
  · intro h
    rw [← h]; ring
  · intro h
    have h' : Nat.card Fx ^ 2 * Nat.card ↥N ^ 2 = Nat.card V * Nat.card ↥N ^ 2 := by
      calc Nat.card Fx ^ 2 * Nat.card ↥N ^ 2 = (Nat.card Fx * Nat.card ↥N) ^ 2 := by ring
        _ = Nat.card V * Nat.card ↥N * Nat.card ↥N := h
        _ = Nat.card V * Nat.card ↥N ^ 2 := by ring
    exact Nat.eq_of_mul_eq_mul_right (pow_pos Nat.card_pos 2) h'

private theorem invol_coset_eq {W : Subgroup G} {t : G} (ht : orderOf t = 2) {n : ℕ}
    {Wseries : ℕ → Subgroup G} (h0 : Wseries 0 = W) (hn : Wseries n = ⊥)
    (hle : ∀ i < n, Wseries (i + 1) ≤ Wseries i)
    (htnorm : ∀ i ≤ n, ∀ g ∈ Wseries i, t * g * t⁻¹ ∈ Wseries i)
    (hcomm : ∀ i < n, ∀ x ∈ Wseries i, ∀ y ∈ Wseries i, ⁅x, y⁆ ∈ Wseries (i + 1))
    (hsq : ∀ i < n, ∀ x ∈ Wseries i, x ^ 2 ∈ Wseries (i + 1))
    (hreg : ∀ i < n, ActsRegularly t (Wseries (i + 1)) (Wseries i)) :
    {j : G | (∃ s ∈ W, j = t * s) ∧ orderOf j = 2} = {j : G | ∃ w ∈ W, j = w * t * w⁻¹} := by
  have ht2 : t * t = 1 := CFSG.GH74.GLS.Bg.TwoGroups.mul_self_eq_one_of_orderOf_eq_two ht
  have hWt : ∀ g ∈ W, t * g * t⁻¹ ∈ W := by
    intro g hg
    have := htnorm 0 (Nat.zero_le n) g (by rw [h0]; exact hg)
    rwa [h0] at this
  have hfree : ∀ i < n, CFSG.GH74.GLS.Bg.TwoGroups.FreeSec2 t (Wseries (n - i))
      (Wseries (n - (i + 1))) := by
    intro i hi
    set j : ℕ := n - i - 1 with hj
    have hjlt : j < n := by omega
    have hi1 : n - i = j + 1 := by omega
    have hi2 : n - (i + 1) = j := by omega
    have hcard := (actsRegularly_iff_card ht (hle j hjlt) (hcomm j hjlt) (hsq j hjlt)
      (htnorm (j + 1) (by omega)) (htnorm j (by omega))).mp (hreg j hjlt)
    have hcard' : Nat.card {g : G // g ∈ Wseries j ∧
        g⁻¹ * (t * g * t⁻¹) ∈ Wseries (j + 1)} ^ 2
        = Nat.card ↥(Wseries j) * Nat.card ↥(Wseries (j + 1)) := by
      rw [← card_fix_comm (hcomm j hjlt) (htnorm j (by omega))]
      exact hcard
    have hbase : CFSG.GH74.GLS.Bg.TwoGroups.FreeSec2 t (Wseries (j + 1)) (Wseries j) :=
      ⟨hle j hjlt, hcomm j hjlt, hsq j hjlt, htnorm (j + 1) (by omega),
        htnorm j (by omega), hcard'⟩
    rw [hi1, hi2]
    exact hbase
  ext j
  constructor
  · rintro ⟨⟨s, hsW, hjs⟩, hjord⟩
    have hjt : j * t⁻¹ ∈ W := by
      have := htnorm 0 (Nat.zero_le n) s (by rw [h0]; exact hsW)
      rw [h0] at this
      rw [hjs]; exact this
    have hj2 : j ^ 2 = 1 := by
      rw [pow_two]
      exact CFSG.GH74.GLS.Bg.TwoGroups.mul_self_eq_one_of_orderOf_eq_two hjord
    obtain ⟨c, hcW, hc⟩ := CFSG.GH74.GLS.Bg.TwoGroups.ig_10_31 G W t n
      (fun k => Wseries (n - k)) ht hWt (by simp [hn]) (by simp [h0]) hfree j hjt hj2
    exact ⟨c, hcW, hc.symm⟩
  · rintro ⟨w, hwW, rfl⟩
    constructor
    · refine ⟨t * (w * t * w⁻¹), ?_, ?_⟩
      · have h1 : t * (w * t * w⁻¹) = (t * w * t⁻¹) * w⁻¹ := by
          calc t * (w * t * w⁻¹) = (t * w * t⁻¹) * (t * t) * w⁻¹ := by group
            _ = (t * w * t⁻¹) * w⁻¹ := by rw [ht2]; group
        rw [h1]
        exact W.mul_mem (hWt w hwW) (W.inv_mem hwW)
      · calc w * t * w⁻¹ = 1 * (w * t * w⁻¹) := by rw [one_mul]
          _ = (t * t) * (w * t * w⁻¹) := by rw [ht2]
          _ = t * (t * (w * t * w⁻¹)) := by rw [mul_assoc]
    · have hconj : SemiconjBy w t (w * t * w⁻¹) := by
        show w * t = (w * t * w⁻¹) * w
        group
      rw [← SemiconjBy.orderOf_eq w hconj]
      exact ht

private theorem card_cent_aux (t : G) (ht : orderOf t = 2) :
    ∀ (n : ℕ) (Wseries : ℕ → Subgroup G), Wseries n = ⊥ →
      (∀ i < n, Wseries (i + 1) ≤ Wseries i) →
      (∀ i ≤ n, ∀ g ∈ Wseries i, t * g * t⁻¹ ∈ Wseries i) →
      (∀ i < n, ∀ x ∈ Wseries i, ∀ y ∈ Wseries i, ⁅x, y⁆ ∈ Wseries (i + 1)) →
      (∀ i < n, ∀ x ∈ Wseries i, x ^ 2 ∈ Wseries (i + 1)) →
      (∀ i < n, ActsRegularly t (Wseries (i + 1)) (Wseries i)) →
      Nat.card ↥(Wseries 0 ⊓ Subgroup.centralizer ({t} : Set G)) ^ 2
        = Nat.card ↥(Wseries 0) := by
  intro n
  induction n with
  | zero =>
    intro Wseries hn _ _ _ _ _
    rw [hn]
    simp
  | succ n ih =>
    intro Wseries hn hle htnorm hcomm hsq hreg
    have hW1 : Wseries 1 ≤ Wseries 0 := hle 0 (Nat.succ_pos n)
    have ht2 : t * t = 1 := CFSG.GH74.GLS.Bg.TwoGroups.mul_self_eq_one_of_orderOf_eq_two ht
    have ih' := ih (fun i => Wseries (i + 1))
      (by simpa using hn)
      (fun i hi => hle (i + 1) (by omega))
      (fun i hi g hg => htnorm (i + 1) (by omega) g hg)
      (fun i hi => hcomm (i + 1) (by omega))
      (fun i hi => hsq (i + 1) (by omega))
      (fun i hi => hreg (i + 1) (by omega))
    have hcard := (actsRegularly_iff_card ht (hle 0 (Nat.succ_pos n))
      (hcomm 0 (Nat.succ_pos n)) (hsq 0 (Nat.succ_pos n))
      (htnorm 1 (by omega)) (htnorm 0 (by omega))).mp (hreg 0 (Nat.succ_pos n))
    let C : Subgroup G := Wseries 0 ⊓ Subgroup.centralizer ({t} : Set G)
    let C' : Subgroup G := Wseries 1 ⊓ Subgroup.centralizer ({t} : Set G)
    let Cb : Subgroup G :=
      { carrier := {g | g ∈ Wseries 0 ∧ ⁅t, g⁆ ∈ Wseries 1}
        one_mem' := ⟨(Wseries 0).one_mem, by simp⟩
        mul_mem' := by
          intro a b ha hb
          have hnorm : ∀ m ∈ Wseries 0, ∀ r ∈ Wseries 1, m * r * m⁻¹ ∈ Wseries 1 := by
            intro m hm r hr
            have e : m * r * m⁻¹ = ⁅m, r⁆ * r := by
              simp only [commutatorElement_def]; group
            rw [e]
            exact (Wseries 1).mul_mem (hcomm 0 (Nat.succ_pos n) m hm r (hW1 hr)) hr
          refine ⟨(Wseries 0).mul_mem ha.1 hb.1, ?_⟩
          have e : ⁅t, a * b⁆ = ⁅t, a⁆ * (a * ⁅t, b⁆ * a⁻¹) := by
            simp only [commutatorElement_def]; group
          rw [e]
          exact (Wseries 1).mul_mem ha.2 (hnorm a ha.1 _ hb.2)
        inv_mem' := by
          intro g hg
          refine ⟨(Wseries 0).inv_mem hg.1, ?_⟩
          have hs : t * g * t⁻¹ ∈ Wseries 0 := htnorm 0 (Nat.zero_le (n + 1)) g hg.1
          have h2 : g⁻¹ * (t * g * t⁻¹) ∈ Wseries 1 :=
            (mul_commutator_mem_iff (hcomm 0 (Nat.succ_pos n)) hs
              ((Wseries 0).inv_mem hg.1)).mp
                (by simpa only [commutatorElement_def] using hg.2)
          have e : ⁅t, g⁻¹⁆ = (t * g * t⁻¹)⁻¹ * g := by
            simp only [commutatorElement_def]; group
          rw [e]
          rw [show (t * g * t⁻¹)⁻¹ * g = (g⁻¹ * (t * g * t⁻¹))⁻¹ by group]
          exact (Wseries 1).inv_mem h2 }
    have hC'_eq : C ⊓ Wseries 1 = C' := by
      ext x
      change x ∈ (Wseries 0 ⊓ Subgroup.centralizer ({t} : Set G)) ⊓ Wseries 1 ↔
        x ∈ Wseries 1 ⊓ Subgroup.centralizer ({t} : Set G)
      simp only [Subgroup.mem_inf]
      constructor
      · rintro ⟨⟨_, hxc⟩, hx1⟩
        exact ⟨hx1, hxc⟩
      · rintro ⟨hx1, hxc⟩
        exact ⟨⟨hW1 hx1, hxc⟩, hx1⟩
    have hCb_eq : Cb = C ⊔ Wseries 1 := by
      refine le_antisymm ?_ (sup_le ?_ ?_)
      · intro g hg
        have hginv : ⁅t, g⁻¹⁆ ∈ Wseries 1 := (Cb.inv_mem hg).2
        have hyt : g⁻¹ * t * g * t⁻¹ ∈ Wseries 1 := by
          have e : g⁻¹ * t * g * t⁻¹ = ⁅t, g⁻¹⁆⁻¹ := by
            simp only [commutatorElement_def]; group
          rw [e]
          exact (Wseries 1).inv_mem hginv
        have hy2 : (g⁻¹ * t * g) ^ 2 = 1 := by
          rw [pow_two]
          calc (g⁻¹ * t * g) * (g⁻¹ * t * g) = g⁻¹ * t * (g * g⁻¹) * t * g := by group
            _ = g⁻¹ * (t * t) * g := by group
            _ = 1 := by rw [ht2]; group
        have hyne : g⁻¹ * t * g ≠ 1 := by
          intro h
          have ht1 : t = 1 := by
            calc t = g * (g⁻¹ * t * g) * g⁻¹ := by group
              _ = 1 := by rw [h]; group
          rw [ht1, orderOf_one] at ht
          omega
        have hyord : orderOf (g⁻¹ * t * g) = 2 :=
          orderOf_eq_prime (p := 2) hy2 hyne
        have hsW1 : t * (g⁻¹ * t * g) ∈ Wseries 1 := by
          have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
          have e : t * (g⁻¹ * t * g) = t * (g⁻¹ * t * g * t⁻¹) * t⁻¹ := by
            calc t * (g⁻¹ * t * g) = t * (g⁻¹ * t * g) * (t * t) := by rw [ht2, mul_one]
              _ = t * (g⁻¹ * t * g * t⁻¹) * t⁻¹ := by rw [htinv]; group
          rw [e]
          exact htnorm 1 (by omega) _ hyt
        have hyL : g⁻¹ * t * g ∈
            {j : G | (∃ s ∈ Wseries 1, j = t * s) ∧ orderOf j = 2} :=
          ⟨⟨t * (g⁻¹ * t * g), hsW1,
              by rw [← mul_assoc t t (g⁻¹ * t * g), ht2, one_mul]⟩, hyord⟩
        have hshift := invol_coset_eq (W := Wseries 1) (t := t) ht (n := n)
          (Wseries := fun i => Wseries (i + 1)) (by simp) (by simpa using hn)
          (fun i hi => hle (i + 1) (by omega))
          (fun i hi g hg => htnorm (i + 1) (by omega) g hg)
          (fun i hi => hcomm (i + 1) (by omega))
          (fun i hi => hsq (i + 1) (by omega))
          (fun i hi => hreg (i + 1) (by omega))
        have hyR : g⁻¹ * t * g ∈ {j : G | ∃ w ∈ Wseries 1, j = w * t * w⁻¹} := by
          rw [← hshift]; exact hyL
        obtain ⟨u, hu1, hyu⟩ := hyR
        have hguC : g * u ∈ C := by
          have hconj : (g * u) * t * (g * u)⁻¹ = t := by
            calc (g * u) * t * (g * u)⁻¹ = g * (u * t * u⁻¹) * g⁻¹ := by group
              _ = g * (g⁻¹ * t * g) * g⁻¹ := by rw [← hyu]
              _ = t := by group
          refine ⟨(Wseries 0).mul_mem hg.1 (hW1 hu1), ?_⟩
          exact Subgroup.mem_centralizer_singleton_iff.mpr (by
            calc (g * u) * t = ((g * u) * t * (g * u)⁻¹) * (g * u) := by group
              _ = t * (g * u) := by rw [hconj])
        have hg_eq : g = (g * u) * u⁻¹ := by group
        rw [hg_eq]
        exact (C ⊔ Wseries 1).mul_mem (Subgroup.mem_sup_left hguC)
          (Subgroup.mem_sup_right ((Wseries 1).inv_mem hu1))
      · intro c hc
        refine ⟨hc.1, ?_⟩
        have hct : t * c * t⁻¹ = c := by
          have h := (Subgroup.mem_centralizer_iff.mp hc.2) t (Set.mem_singleton t)
          calc t * c * t⁻¹ = (c * t) * t⁻¹ := by rw [← h]
            _ = c := by group
        have e : ⁅t, c⁆ = (t * c * t⁻¹) * c⁻¹ := rfl
        rw [e, hct, mul_inv_cancel]
        exact (Wseries 1).one_mem
      · intro r hr
        refine ⟨hW1 hr, ?_⟩
        have e : ⁅t, r⁆ = (t * r * t⁻¹) * r⁻¹ := rfl
        rw [e]
        exact (Wseries 1).mul_mem (htnorm 1 (by omega) r hr) ((Wseries 1).inv_mem hr)
    have hcardCb : Nat.card {g : G // g ∈ Wseries 0 ∧ ⁅t, g⁆ ∈ Wseries 1} = Nat.card ↥Cb := rfl
    have hC'card : Nat.card ↥C' ^ 2 = Nat.card ↥(Wseries 1) := by
      simpa only [C'] using ih'
    haveI : ((Wseries 1).subgroupOf (Wseries 0)).Normal := by
      rw [Subgroup.normal_subgroupOf_iff hW1]
      intro a b ha hb
      have e : b * a * b⁻¹ = ⁅b, a⁆ * a := by
        simp only [commutatorElement_def]; group
      rw [e]
      exact (Wseries 1).mul_mem (hcomm 0 (Nat.succ_pos n) b hb a (hW1 ha)) ha
    let CW : Subgroup (Wseries 0) := C.subgroupOf (Wseries 0)
    let NW : Subgroup (Wseries 0) := (Wseries 1).subgroupOf (Wseries 0)
    have hrel : Nat.card ↥(CW ⊔ NW) * Nat.card ↥(CW ⊓ NW)
        = Nat.card ↥CW * Nat.card ↥NW := by
      have h1 : NW.relIndex CW * Nat.card ↥(CW ⊓ NW) = Nat.card ↥CW := by
        have h := Subgroup.relIndex_mul_card (H := NW) (K := CW)
        rwa [inf_comm] at h
      have h2 : NW.relIndex CW * Nat.card ↥NW = Nat.card ↥(CW ⊔ NW) := by
        have h := Subgroup.relIndex_mul_card (H := NW) (K := CW ⊔ NW)
        rw [Subgroup.relIndex_sup_right] at h
        rwa [inf_eq_left.mpr le_sup_right] at h
      calc Nat.card ↥(CW ⊔ NW) * Nat.card ↥(CW ⊓ NW)
          = (NW.relIndex CW * Nat.card ↥NW) * Nat.card ↥(CW ⊓ NW) := by rw [h2]
        _ = Nat.card ↥NW * (NW.relIndex CW * Nat.card ↥(CW ⊓ NW)) := by ring
        _ = Nat.card ↥NW * Nat.card ↥CW := by rw [h1]
        _ = Nat.card ↥CW * Nat.card ↥NW := by ring
    have hCWcard : Nat.card ↥CW = Nat.card ↥C :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : C ≤ Wseries 0)).toEquiv
    have hNWcard : Nat.card ↥NW = Nat.card ↥(Wseries 1) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW1).toEquiv
    have hCWsup : Nat.card ↥(CW ⊔ NW) = Nat.card ↥(C ⊔ Wseries 1) := by
      have e : (C ⊔ Wseries 1).subgroupOf (Wseries 0) = CW ⊔ NW :=
        Subgroup.subgroupOf_sup (inf_le_left : C ≤ Wseries 0) hW1
      rw [← e]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe
        (sup_le (inf_le_left : C ≤ Wseries 0) hW1)).toEquiv
    have hCWinf : Nat.card ↥(CW ⊓ NW) = Nat.card ↥(C ⊓ Wseries 1) := by
      have e : (C ⊓ Wseries 1).subgroupOf (Wseries 0) = CW ⊓ NW := by
        ext x
        simp only [Subgroup.mem_inf, Subgroup.mem_subgroupOf]
        tauto
      rw [← e]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe
        (le_trans (inf_le_left : C ⊓ Wseries 1 ≤ C)
          (inf_le_left : C ≤ Wseries 0))).toEquiv
    have hprod : Nat.card ↥(C ⊔ Wseries 1) * Nat.card ↥(C ⊓ Wseries 1)
        = Nat.card ↥C * Nat.card ↥(Wseries 1) := by
      rw [← hCWsup, ← hCWinf, ← hCWcard, ← hNWcard]
      exact hrel
    have hrel' : Nat.card ↥Cb * Nat.card ↥C' = Nat.card ↥C * Nat.card ↥(Wseries 1) := by
      rw [hCb_eq, ← hC'_eq]; exact hprod
    have hcard' : Nat.card ↥Cb ^ 2 = Nat.card ↥(Wseries 0) * Nat.card ↥(Wseries 1) := by
      rw [← hcardCb]; exact hcard
    have hrel2 : Nat.card ↥C * Nat.card ↥(Wseries 1) = Nat.card ↥C' * Nat.card ↥Cb := by
      rw [← hrel']; ring
    show Nat.card ↥C ^ 2 = Nat.card ↥(Wseries 0)
    have h1 : Nat.card ↥C ^ 2 * Nat.card ↥(Wseries 1) ^ 2
        = Nat.card ↥(Wseries 1) * (Nat.card ↥(Wseries 0) * Nat.card ↥(Wseries 1)) := by
      calc Nat.card ↥C ^ 2 * Nat.card ↥(Wseries 1) ^ 2
          = (Nat.card ↥C * Nat.card ↥(Wseries 1)) ^ 2 := by ring
        _ = (Nat.card ↥C' * Nat.card ↥Cb) ^ 2 := by rw [hrel2]
        _ = Nat.card ↥C' ^ 2 * Nat.card ↥Cb ^ 2 := by ring
        _ = Nat.card ↥(Wseries 1) * (Nat.card ↥(Wseries 0) * Nat.card ↥(Wseries 1)) := by
              rw [hC'card, hcard']
    have h2 : Nat.card ↥C ^ 2 * Nat.card ↥(Wseries 1) ^ 2
        = Nat.card ↥(Wseries 0) * Nat.card ↥(Wseries 1) ^ 2 := by
      calc Nat.card ↥C ^ 2 * Nat.card ↥(Wseries 1) ^ 2
          = Nat.card ↥(Wseries 1) * (Nat.card ↥(Wseries 0) * Nat.card ↥(Wseries 1)) := h1
        _ = Nat.card ↥(Wseries 0) * Nat.card ↥(Wseries 1) ^ 2 := by ring
    exact Nat.eq_of_mul_eq_mul_right (pow_pos Nat.card_pos 2) h2

theorem lemma36 (W : Subgroup G) (t : G) (ht : orderOf t = 2) (n : ℕ)
    (Wseries : ℕ → Subgroup G) (h0 : Wseries 0 = W) (hn : Wseries n = ⊥)
    (hle : ∀ i < n, Wseries (i + 1) ≤ Wseries i)
    (htnorm : ∀ i ≤ n, ∀ g ∈ Wseries i, t * g * t⁻¹ ∈ Wseries i)
    (hcomm : ∀ i < n, ∀ x ∈ Wseries i, ∀ y ∈ Wseries i, ⁅x, y⁆ ∈ Wseries (i + 1))
    (hsq : ∀ i < n, ∀ x ∈ Wseries i, x ^ 2 ∈ Wseries (i + 1))
    (hreg : ∀ i < n, ActsRegularly t (Wseries (i + 1)) (Wseries i)) :
    {j : G | (∃ s ∈ W, j = t * s) ∧ orderOf j = 2} = {j : G | ∃ w ∈ W, j = w * t * w⁻¹} ∧
      Nat.card ↥(W ⊓ Subgroup.centralizer ({t} : Set G)) ^ 2 = Nat.card ↥W := by
  constructor
  · exact invol_coset_eq ht h0 hn hle htnorm hcomm hsq hreg
  · have h := card_cent_aux t ht n Wseries hn hle htnorm hcomm hsq hreg
    rw [← h0]
    exact h

end Lemma36

end CFSG.OddStandard.SmallF3.HarrisU33
