module

public import CFSG.ClassicalInvolution.ModelFacts.ChevAutTorusDiag
public import CFSG.ClassicalInvolution.ModelFacts.ChevAutTorusStdBasic
public import CFSG.ClassicalInvolution.ModelFacts.ChevAutTorusStdNum
public import CFSG.ClassicalInvolution.ModelFacts.ChevAutTorusStdRoots

public section

namespace CFSG.ClassicalInvolution.ModelFacts.ChevAut

open CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.RootSystem
  CFSG.LieType.Steinberg

section Sub

variable {K : Type*} [Group K] {D : UniversalRootDatum K} {F : Type} [Field F]
  {x : (Fin D.rank → ℤ) → F → K} {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K}

@[expose] def subTorus (x : (Fin D.rank → ℤ) → F → K) (m : Fin D.rank → ℕ) : Subgroup K :=
  Subgroup.closure {t | ∃ (i : Fin D.rank) (s : Fˣ), t = torusGen x i (s ^ m i)}

theorem torusGen_pow_mem_subTorus (m : Fin D.rank → ℕ) (i : Fin D.rank) (s : Fˣ) :
    torusGen x i (s ^ m i) ∈ subTorus x m :=
  Subgroup.subset_closure ⟨i, s, rfl⟩

theorem subTorus_le (hS : TorusSetup D x n H) (m : Fin D.rank → ℕ) :
    subTorus x m ≤ ⨆ i, H i := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨i, s, rfl⟩
  exact hS.torusGen_mem i _

theorem TorusSetup.hno_sub [Finite F] (hS : TorusSetup D x n H) (hq : 5 ≤ Nat.card F)
    (hlong : ∀ k, IsLongest D.isFiniteType ∅ (Pi.single k 1))
    (hnb : ∀ k, ∃ j, D.cartan j k = -1) (m : Fin D.rank → ℕ) (hm : ∀ j, m j = 1 ∨ m j = 2) :
    ∀ γ ∈ D.roots, ∃ t ∈ subTorus x m, ∀ y ∈ D.rootGroup γ, t * y * t⁻¹ = y → y = 1 := by
  obtain ⟨C, O, hE⟩ := hS.chev
  intro γ hγ
  have hγ' : γ ∈ roots D.isFiniteType ∅ := by rw [← hS.div]; exact hγ
  obtain ⟨j, hj⟩ := exists_odd_pair D.isFiniteType hlong hnb hγ'
  have hbd := abs_pair_le D.isFiniteType hlong hγ' j
  obtain ⟨ζ, hζ⟩ := IsCyclic.exists_generator (α := Fˣ)
  have hord : orderOf ζ = Nat.card F - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hζ, Nat.card_units]
  refine ⟨torusGen x j (ζ ^ m j), torusGen_pow_mem_subTorus m j ζ, fun y hy hfix => ?_⟩
  obtain ⟨u, rfl⟩ := ((hE.param γ hγ).1 y).1 hy
  have hact := torusGen_act hE hγ j (ζ ^ m j) u
  have h3 := (hE.param γ hγ).2.2 (hact.symm.trans hfix)
  have hne : ((ζ ^ m j) ^ (∑ l, D.cartan j l * γ l) : Fˣ) ≠ 1 := by
    intro h1
    have h2 : ζ ^ ((m j : ℤ) * (∑ l, D.cartan j l * γ l)) = 1 := by
      rw [zpow_mul, zpow_natCast]
      exact h1
    have h3 : ((Nat.card F - 1 : ℕ) : ℤ) ∣ (m j : ℤ) * (∑ l, D.cartan j l * γ l) := by
      rw [← hord]
      exact orderOf_dvd_iff_zpow_eq_one.2 h2
    have hc : (∑ l, D.cartan j l * γ l) = 1 ∨ (∑ l, D.cartan j l * γ l) = -1 := by
      have hodd := Int.not_even_iff_odd.1 hj
      change |∑ l, D.cartan j l * γ l| ≤ 2 at hbd
      change Odd (∑ l, D.cartan j l * γ l) at hodd
      rw [abs_le] at hbd
      obtain ⟨t, ht⟩ := hodd
      omega
    have hq4 : (4 : ℤ) ≤ ((Nat.card F - 1 : ℕ) : ℤ) := by omega
    have hmj := hm j
    have h0 := Int.eq_zero_of_abs_lt_dvd h3 (by
      rcases hc with h | h <;> rcases hmj with h' | h' <;> rw [h, h'] <;> simp <;> omega)
    rcases hc with h | h <;> rcases hmj with h' | h' <;> rw [h, h'] at h0 <;> simp at h0
  have h4 : (((ζ ^ m j) ^ (∑ l, D.cartan j l * γ l) : Fˣ) : F) * u = u := h3
  have h5 : ((((ζ ^ m j) ^ (∑ l, D.cartan j l * γ l) : Fˣ) : F) - 1) * u = 0 := by
    linear_combination h4
  have h6 : u = 0 := by
    rcases mul_eq_zero.1 h5 with h | h
    · exact absurd (Units.ext (by simpa [sub_eq_zero] using h)) hne
    · exact h
  rw [h6]
  have h7 := (hE.param γ hγ).2.1 0 0
  rw [add_zero] at h7
  exact (mul_left_cancel (a := x γ 0) (by rw [mul_one]; exact h7)).symm


variable {α : K →* K} {g : K} {a : Fin D.rank → Fˣ} {φ : F ≃+* F} {π : Equiv.Perm (Fin D.rank)}

theorem alpha_torusGen_pow (hS : TorusSetup D x n H) (hN : NormalForm x α g a φ π)
    (i : Fin D.rank) (s : Fˣ) (k : ℕ) :
    α (torusGen x i (s ^ k)) =
      g * torusGen x (π i) (Units.map (φ : F →+* F) s ^ k) * g⁻¹ := by
  rw [alpha_torusGen hS.hom hN.pos hN.neg, map_pow]

theorem conj_mem_of_alpha_sub (hS : TorusSetup D x n H) (hN : NormalForm x α g a φ π)
    (m : Fin D.rank → ℕ) (hπm : ∀ j, m (π j) = m j)
    (hfix : ∀ i s, α (torusGen x i (s ^ m i)) * (torusGen x i (s ^ m i))⁻¹ ∈
      Subgroup.center K) :
    ∀ t ∈ subTorus x m, g * t * g⁻¹ ∈ ⨆ i, H i := by
  have hgen : ∀ (i' : Fin D.rank) (s' : Fˣ), g * torusGen x i' (s' ^ m i') * g⁻¹ ∈ ⨆ i, H i := by
    intro i' s'
    have h0 := alpha_torusGen_pow hS hN (π.symm i') (Units.map (φ.symm : F →+* F) s')
      (m (π.symm i'))
    rw [Equiv.apply_symm_apply] at h0
    have h2 : (Units.map (φ : F →+* F) (Units.map (φ.symm : F →+* F) s' : Fˣ) : Fˣ) = s' := by
      ext; simp
    rw [h2] at h0
    have hmi : m (π.symm i') = m i' := by
      have := hπm (π.symm i')
      rw [Equiv.apply_symm_apply] at this
      exact this.symm
    have h0' : g * torusGen x i' (s' ^ m i') * g⁻¹ =
        α (torusGen x (π.symm i') (Units.map (φ.symm : F →+* F) s' ^ m (π.symm i'))) := by
      rw [h0, hmi]
    rw [h0']
    have h3 := mul_mem
      (hS.center_le (hfix (π.symm i') (Units.map (φ.symm : F →+* F) s')))
      (hS.torusGen_mem (π.symm i') (Units.map (φ.symm : F →+* F) s' ^ m (π.symm i')))
    rwa [inv_mul_cancel_right] at h3
  intro t ht
  have hle : subTorus x m ≤ (⨆ i, H i).comap (MulAut.conj g).toMonoidHom := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨i, s, rfl⟩
    exact hgen i s
  exact hle ht

theorem char_eq_of_alpha_sub (hS : TorusSetup D x n H) (hN : NormalForm x α g a φ π)
    (m : Fin D.rank → ℕ)
    (hfix : ∀ i s, α (torusGen x i (s ^ m i)) * (torusGen x i (s ^ m i))⁻¹ ∈
      Subgroup.center K)
    {h : K} (hh : h ∈ ⨆ i, H i) {w : (coxeterMatrix D.isFiniteType).Group}
    (hg : g = h * nrep hS.ct w) (j : Fin D.rank) (s : Fˣ) {δ : Fin D.rank → ℤ}
    (hδ : δ ∈ D.roots) :
    Units.map (φ : F →+* F) s ^ ((m j : ℤ) * pair D.cartan δ (π j)) =
      s ^ ((m j : ℤ) * pair D.cartan (weylAction D.isFiniteType w δ) j) := by
  obtain ⟨C, O, hE⟩ := hS.chev
  have hδ' : weylAction D.isFiniteType w δ ∈ D.roots := weylAction_mem_roots D.isFiniteType w hδ
  have h1 := torusGen_act hE hδ (π j) (Units.map (φ : F →+* F) s ^ m j)
  obtain ⟨ε, hε, hεc⟩ := signConj_nrep hE hS.ct hS.n_eq w δ hδ
  have h2 := TAct.conj_of_sign hε hεc h1
  obtain ⟨lam, hlam⟩ := exists_tact_of_mem_iSup hE hS.H_iff hh
  have h3 := TAct.conj (hlam _ hδ') h2
  have h4 : g * torusGen x (π j) (Units.map (φ : F →+* F) s ^ m j) * g⁻¹ =
      h * (nrep hS.ct w * torusGen x (π j) (Units.map (φ : F →+* F) s ^ m j) *
        (nrep hS.ct w)⁻¹) * h⁻¹ := by
    rw [hg]; group
  have h5 := alpha_torusGen_pow hS hN j s (m j)
  have h6 : α (torusGen x j (s ^ m j)) =
      (α (torusGen x j (s ^ m j)) * (torusGen x j (s ^ m j))⁻¹) * torusGen x j (s ^ m j) := by
    group
  have h7 : TAct x (α (torusGen x j (s ^ m j))) (weylAction D.isFiniteType w δ)
      ((s ^ m j) ^ pair D.cartan (weylAction D.isFiniteType w δ) j) := by
    rw [h6]
    exact TAct.central_mul (hfix j s) (torusGen_act hE hδ' j (s ^ m j))
  rw [h5, h4] at h7
  have h8 := TAct.unique (hE.param _ hδ').2.2 h3 h7
  simp only [← zpow_natCast, ← zpow_mul] at h8
  exact h8


theorem eq_one_of_char_eq_sub [Finite F] {p : ℕ} [Fact p.Prime] [CharP F p]
    (hS : TorusSetup D x n H) (hp2 : p ≠ 2) (hq : 5 ≤ Nat.card F) (hr : 0 < D.rank)
    (hlong : ∀ k, IsLongest D.isFiniteType ∅ (Pi.single k 1)) (ν : Fin D.rank)
    (hnb : ∀ k, ∃ j, j ≠ ν ∧ D.cartan j k = -1)
    (hAij : ∀ i j, i ≠ j → D.cartan i j = 0 ∨ D.cartan i j = -1)
    (hπ : ∀ j l, D.cartan (π j) (π l) = D.cartan j l) (hπν : π ν = ν)
    (θ : Fin D.rank → ℤ) (hθ1 : ∀ j, pair D.cartan θ j = if j = ν then 1 else 0)
    (hθ2 : θ ν = 2) (m : Fin D.rank → ℕ) (hm : ∀ j, m j = if j = ν then 2 else 1)
    {w : (coxeterMatrix D.isFiniteType).Group}
    (hchar : ∀ (j : Fin D.rank) (s : Fˣ) (δ : Fin D.rank → ℤ), δ ∈ D.roots →
      Units.map (φ : F →+* F) s ^ ((m j : ℤ) * pair D.cartan δ (π j)) =
        s ^ ((m j : ℤ) * pair D.cartan (weylAction D.isFiniteType w δ) j)) :
    φ = 1 ∧ w = 1 ∧ π = 1 := by
  have hq4 : (4 : ℤ) ≤ ((Nat.card F - 1 : ℕ) : ℤ) := by omega
  have step : ∀ k : Fin D.rank, φ = 1 ∧
      weylAction D.isFiniteType w (Pi.single k 1) = Pi.single (π.symm k) 1 := by
    intro k
    have hπk' : π (π.symm k) = k := Equiv.apply_symm_apply π k
    have hk : (Pi.single k 1 : Fin D.rank → ℤ) ∈ D.roots :=
      (RootSystem.ofCartan D.isFiniteType D.divisible).single_mem k
    have hγ : weylAction D.isFiniteType w (Pi.single k 1) ∈ D.roots :=
      weylAction_mem_roots D.isFiniteType w hk
    have hγ' := roots_empty hS hγ
    obtain ⟨j', hj'ν, hj'⟩ := hnb k
    have hj₁ν : π.symm j' ≠ ν := fun h => hj'ν (by rw [← hπν, ← h]; simp)
    have hm₁ : m (π.symm j') = 1 := by rw [hm]; simp [hj₁ν]
    obtain ⟨hφ, hcd, hcong⟩ := frob_cong_wt hp2 hq φ m (fun j => D.cartan (π j) k)
      (fun j => pair D.cartan (weylAction D.isFiniteType w (Pi.single k 1)) j) (π.symm k)
      (π.symm j') (fun j => abs_pair_le D.isFiniteType hlong hγ' j)
      (fun j hj => hAij (π j) k (fun h => hj (by rw [← h]; simp)))
      (by simp [hj']) hm₁
      (fun s j => by
        have := hchar j s (Pi.single k 1) hk
        rwa [pair_single] at this)
    refine ⟨hφ, ?_⟩
    have hpair_single : ∀ j, pair D.cartan (Pi.single (π.symm k) 1) j = D.cartan (π j) k := by
      intro j
      rw [pair_single, ← hπ j (π.symm k), hπk']
    have hck' : π.symm k ≠ ν →
        pair D.cartan (weylAction D.isFiniteType w (Pi.single k 1)) (π.symm k) = 2 := by
      intro hk'ν
      have hmk' : m (π.symm k) = 1 := by rw [hm]; simp [hk'ν]
      have h1 := hcong (π.symm k)
      simp only [hmk', hπk', D.isFiniteType.apply_self, Nat.cast_one, one_mul] at h1
      have hc2 := abs_pair_le D.isFiniteType hlong hγ' (π.symm k)
      rw [abs_le] at hc2
      by_contra hne
      have hc : pair D.cartan (weylAction D.isFiniteType w (Pi.single k 1)) (π.symm k) = -2 := by
        have hle := Int.le_of_dvd (by omega) h1
        omega
      have hneg := eq_neg_single_of_pair_eq_neg_two D.isFiniteType hlong hγ' hc
      obtain ⟨j'', hj''ν, hj''⟩ := hnb (π.symm k)
      have hne2 : j'' ≠ π.symm k := fun h => by
        rw [h, D.isFiniteType.apply_self] at hj''
        omega
      have h3 := hcd j'' (by rw [hm]; simp [hj''ν]) hne2
      have h4 : D.cartan (π j'') k = -1 := by
        rw [← hj'', ← hπ j'' (π.symm k), hπk']
      rw [hneg, pair_neg, pair_single, hj''] at h3
      omega
    have hoff : ∀ j, j ≠ ν →
        pair D.cartan (weylAction D.isFiniteType w (Pi.single k 1)) j =
          pair D.cartan (Pi.single (π.symm k) 1) j := by
      intro j hjν
      have hmj : m j = 1 := by rw [hm]; simp [hjν]
      by_cases hj : j = π.symm k
      · subst hj
        rw [hck' hjν, pair_single, D.isFiniteType.apply_self]
      · rw [hcd j hmj hj, hpair_single]
    rcases eq_single_or_sub_of_pair_eq D.isFiniteType hlong ν θ hθ1 hθ2 hγ' (π.symm k) hoff with
      h | ⟨hkν, h⟩
    · exact h
    · exfalso
      have hk : k = ν := by rw [← hπk', hkν, hπν]
      subst hk
      have h1 := hcong k
      have hmk : m k = 2 := by rw [hm]; simp
      have hcν : pair D.cartan (weylAction D.isFiniteType w (Pi.single k 1)) k = 1 := by
        rw [h, pair_sub, pair_single, hθ1 k, hkν, D.isFiniteType.apply_self]
        simp
      rw [hmk, hπν, D.isFiniteType.apply_self, hcν] at h1
      have := Int.le_of_dvd (by norm_num) h1
      omega
  have hw1 : w = 1 := by
    by_contra hw
    obtain ⟨i, hi⟩ :=
      (coxeterMatrix D.isFiniteType).toCoxeterSystem.exists_rightDescent_of_ne_one hw
    have h1 := ht_weylAction_single_neg (D := D) hi
    rw [(step i).2] at h1
    have h2 := ht_single_pos (D := D) (π.symm i)
    omega
  refine ⟨(step ⟨0, hr⟩).1, hw1, Equiv.ext fun k => ?_⟩
  have h1 := (step k).2
  rw [hw1, map_one, Module.End.one_apply] at h1
  have h2 : π.symm k = k := by
    by_contra hne
    have := congrFun h1 k
    simp [hne] at this
  have h3 := congrArg π h2
  rw [Equiv.apply_symm_apply] at h3
  simpa using h3.symm


theorem diag_of_normalForm_trivial (hS : TorusSetup D x n H)
    {α : K →* K} {g : K} {a : Fin D.rank → Fˣ}
    (hN : NormalForm x α g a (1 : F ≃+* F) (1 : Equiv.Perm (Fin D.rank)))
    (hh : g ∈ ⨆ i, H i) :
    ∃ b : Fin D.rank → Fˣ, ∀ γ ∈ D.roots, ∀ c, α (x γ c) = x γ ((diagChar b γ : F) * c) := by
  obtain ⟨C, O, hE⟩ := hS.chev
  obtain ⟨lam, hlam⟩ := exists_tact_of_mem_iSup hE hS.H_iff hh
  set b : Fin D.rank → Fˣ := fun i => charVal D.cartan lam (Pi.single i 1) * a i with hb
  have hroot : ∀ i, (Pi.single i 1 : Fin D.rank → ℤ) ∈ D.roots := fun i =>
    (RootSystem.ofCartan D.isFiniteType D.divisible).single_mem i
  have hsimple₁ : ∀ i c, α (x (Pi.single i 1) c) = x (Pi.single i 1) ((b i : F) * c) := by
    intro i c
    rw [hN.pos i c]
    simp only [Equiv.Perm.coe_one, id_eq]
    rw [show (1 : F ≃+* F) c = c from rfl, hlam _ (hroot i)]
    congr 1
    simp [hb]
    ring
  have hsimple₂ : ∀ i c, α (x (-Pi.single i 1) c) =
      x (-Pi.single i 1) ((((b i)⁻¹ : Fˣ) : F) * c) := by
    intro i c
    rw [hN.neg i c]
    simp only [Equiv.Perm.coe_one, id_eq]
    rw [show (1 : F ≃+* F) c = c from rfl,
      hlam _ (CFSG.LieType.Steinberg.OfCartan.neg_mem_roots D.isFiniteType (hroot i)),
      charVal_neg]
    congr 1
    simp [hb]
    ring
  have hbase : ∀ k c, α (x (Pi.single k 1) c) =
      x (Pi.single k 1) ((diagChar b (Pi.single k 1) : F) * c) := by
    intro k c
    rw [diagChar_single]
    exact hsimple₁ k c
  have hw1 : ∀ i, α (weylElement x i 1) = weylElement x i (b i) := by
    intro i
    unfold weylElement
    rw [map_mul, map_mul, hsimple₁ i, hsimple₂ i]
    simp
  have hstep : ∀ (i : Fin D.rank) (δ : Fin D.rank → ℤ), δ ∈ D.roots →
      (∀ c, α (x δ c) = x δ ((diagChar b δ : F) * c)) →
      ∀ c, α (x (reflection D.cartan i δ) c) =
        x (reflection D.cartan i δ) ((diagChar b (reflection D.cartan i δ) : F) * c) := by
    intro i δ hδ hR c
    obtain ⟨ε, hε, hεw⟩ := hE.weyl i δ hδ
    have hε2 : (ε : F) * ε = 1 := by rcases hε with rfl | rfl <;> simp
    have h1 : x (reflection D.cartan i δ) c =
        weylElement x i 1 * x δ ((ε : F) * c) * (weylElement x i 1)⁻¹ := by
      rw [hεw 1 ((ε : F) * c)]
      congr 1
      simp
      linear_combination (-c) * hε2
    rw [h1, map_mul, map_mul, hR, hw1, map_inv, hw1, hεw (b i)]
    congr 1
    rw [diagChar_reflection]
    simp only [Units.val_mul, pair]
    linear_combination ((diagChar b δ : F) * ((b i ^ (-∑ l, D.cartan i l * δ l) : Fˣ) : F) * c)
      * hε2
  refine ⟨b, fun γ hγ => ?_⟩
  have key : ∀ (k : Fin D.rank) (ω : List (Fin D.rank)), ∀ c,
      α (x (weylAction D.isFiniteType
        ((coxeterMatrix D.isFiniteType).toCoxeterSystem.wordProd ω) (Pi.single k 1)) c) =
      x (weylAction D.isFiniteType
        ((coxeterMatrix D.isFiniteType).toCoxeterSystem.wordProd ω) (Pi.single k 1))
        ((diagChar b (weylAction D.isFiniteType
          ((coxeterMatrix D.isFiniteType).toCoxeterSystem.wordProd ω) (Pi.single k 1)) : F) *
          c) := by
    intro k ω
    induction ω with
    | nil => simpa using hbase k
    | cons i ω ih =>
      rw [CoxeterSystem.wordProd_cons, weylAction_mul_apply, weylAction_simple]
      exact hstep i _ (weylAction_mem_roots D.isFiniteType _ (hroot k)) ih
  have hγ0 : γ ∈ roots D.isFiniteType D.divisible := hγ
  rcases hγ0 with ⟨w, k, rfl⟩ | ⟨w, k, hk, rfl⟩
  · obtain ⟨ω, -, rfl⟩ := (coxeterMatrix D.isFiniteType).toCoxeterSystem.exists_isReduced w
    exact key k ω
  · rw [hS.div] at hk
    exact absurd hk (Set.notMem_empty _)


theorem exists_diag_of_fixes_subtorus [Finite F] {p : ℕ} [Fact p.Prime] [CharP F p]
    (hS : TorusSetup D x n H) (hp2 : p ≠ 2) (hq : 5 ≤ Nat.card F) (hr : 0 < D.rank)
    (hlong : ∀ k, IsLongest D.isFiniteType ∅ (Pi.single k 1)) (ν : Fin D.rank)
    (hnb : ∀ k, ∃ j, j ≠ ν ∧ D.cartan j k = -1)
    (hAij : ∀ i j, i ≠ j → D.cartan i j = 0 ∨ D.cartan i j = -1)
    (hπ : ∀ j l, D.cartan (π j) (π l) = D.cartan j l) (hπν : π ν = ν)
    (θ : Fin D.rank → ℤ) (hθ1 : ∀ j, pair D.cartan θ j = if j = ν then 1 else 0)
    (hθ2 : θ ν = 2) (m : Fin D.rank → ℕ) (hm : ∀ j, m j = if j = ν then 2 else 1)
    (hN : NormalForm x α g a φ π)
    (hfix : ∀ i s, α (torusGen x i (s ^ m i)) * (torusGen x i (s ^ m i))⁻¹ ∈
      Subgroup.center K) :
    ∃ b : Fin D.rank → Fˣ, ∀ γ ∈ D.roots, ∀ c, α (x γ c) = x γ ((diagChar b γ : F) * c) := by
  have hmpm : ∀ j, m j = 1 ∨ m j = 2 := fun j => by
    rw [hm]
    split_ifs <;> simp
  have hπm : ∀ j, m (π j) = m j := fun j => by
    rw [hm, hm]
    have : π j = ν ↔ j = ν :=
      ⟨fun h => π.injective (h.trans hπν.symm), fun h => h ▸ hπν⟩
    simp only [this]
  have hno := hS.hno_sub hq hlong (fun k => (hnb k).imp fun j h => h.2) m hmpm
  obtain ⟨h, hh, w, hg⟩ := exists_mem_mul_nrep_of_forall_conj_mem_of_le hS.ct hS.ext hS.bru
    (subTorus_le hS m) hno (conj_mem_of_alpha_sub hS hN m hπm hfix)
  obtain ⟨hφ, hw, hπ1⟩ := eq_one_of_char_eq_sub hS hp2 hq hr hlong ν hnb hAij hπ hπν θ hθ1 hθ2 m
    hm (fun j s δ hδ => char_eq_of_alpha_sub hS hN m hfix hh hg j s hδ)
  subst hw hπ1 hφ
  rw [nrep_one, mul_one] at hg
  subst hg
  exact diag_of_normalForm_trivial hS hN hh

end Sub

end CFSG.ClassicalInvolution.ModelFacts.ChevAut
