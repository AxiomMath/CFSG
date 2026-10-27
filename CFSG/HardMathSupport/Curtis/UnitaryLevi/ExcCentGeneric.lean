module

public import CFSG.HardMathSupport.Curtis.UnitaryLevi.ExcTorusAct
public import CFSG.HardMathSupport.Curtis.UnitaryLevi.ExcWeylWords
public import CFSG.HardMathSupport.Curtis.UnitaryLevi.ExcCentAbstract

public section

namespace CFSG.HardMathSupport.Curtis.UnitaryLevi

open CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley CFSG.RankThree.CentralCover

section Mact

variable {K : Type} [Field K] [Finite K] {r : ℕ}

theorem mact_one_vec (M : Matrix (Fin r) (Fin r) ℤ) : mact K M (1 : Fin r → Kˣ) = 1 := by
  ext1 k
  simp [mact]

theorem mact_neg (M : Matrix (Fin r) (Fin r) ℤ) (t : Fin r → Kˣ) :
    mact K (-M) t = (mact K M t)⁻¹ := by
  ext1 k
  simp [mact, Finset.prod_inv_distrib]

theorem mact_sub (M N : Matrix (Fin r) (Fin r) ℤ) (t : Fin r → Kˣ) :
    mact K (M - N) t = mact K M t * (mact K N t)⁻¹ := by
  rw [sub_eq_add_neg, mact_add, mact_neg]

theorem mact_one_sub (X : Matrix (Fin r) (Fin r) ℤ) (t : Fin r → Kˣ) :
    mact K (1 - X) t = t * (mact K X t)⁻¹ := by
  rw [mact_sub, mact_one]

theorem mact_smul_one (c : ℤ) (t : Fin r → Kˣ) :
    mact K (c • (1 : Matrix (Fin r) (Fin r) ℤ)) t = t ^ c := by
  ext1 k
  simp [mact, Matrix.smul_apply, Matrix.one_apply, Finset.prod_ite_eq]

@[expose] def mactHom (M : Matrix (Fin r) (Fin r) ℤ) : (Fin r → Kˣ) →* (Fin r → Kˣ) where
  toFun := mact K M
  map_one' := mact_one_vec M
  map_mul' := mact_mul_apply M

@[simp] theorem mactHom_apply (M : Matrix (Fin r) (Fin r) ℤ) (t : Fin r → Kˣ) :
    mactHom M t = mact K M t := rfl

@[expose] def vecT (w : Fin r → ℤ) (g : Kˣ) : Fin r → Kˣ := fun i => g ^ w i

theorem mact_vecT (M : Matrix (Fin r) (Fin r) ℤ) (w : Fin r → ℤ) (g : Kˣ) :
    mact K M (vecT w g) = vecT (M.mulVec w) g := by
  ext1 k
  simp only [mact, vecT, ← zpow_mul, Matrix.mulVec, dotProduct]
  rw [← prod_zpow_sum_aux]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [mul_comm]

theorem vecT_eq_of_dvd (w w' : Fin r → ℤ) (ω : Kˣ) (hω : orderOf ω = 3)
    (h : ∀ i, (3 : ℤ) ∣ w i - w' i) : vecT w ω = vecT w' ω := by
  ext1 k
  simp only [vecT]
  rw [zpow_eq_zpow_iff_modEq, hω]
  exact (Int.modEq_iff_dvd.2 (by simpa using (h k))).symm

end Mact

section Torus

variable (τ : Tag) (K : Type) [Field K] [Finite K]

theorem psi_wordProd (l : List (Fin τ.rank)) :
    monomialSubHom (τ := τ) (K := K) (l.map (weylRep τ K)).prod = wordW τ l := by
  induction l with
  | nil => simp [wordW]
  | cons i l ih =>
    rw [List.map_cons, List.prod_cons, map_mul, ih, monomialSubHom_weylRep]
    simp [wordW]

theorem exists_torusN_of_psi_eq_one {x : ↥(monomialSub τ K)}
    (hx : monomialSubHom (τ := τ) (K := K) x = 1) : ∃ t, torusN τ K t = x := by
  have hx' : x ∈ (monomialSubHom (τ := τ) (K := K)).ker := hx
  rw [monomialSubHom_ker, Subgroup.mem_subgroupOf, borelSub_inf_monomialSub] at hx'
  have hxt : ((x : adjointGroup τ K) : ModGL τ K) ∈ torusGroup τ K := hx'
  obtain ⟨t, ht⟩ := torusCoordHom_surjective (τ := τ) (R := K) ⟨_, hxt⟩
  refine ⟨t, monoι_injective τ K ?_⟩
  rw [monoι_torusN]
  exact congrArg Subtype.val ht

theorem psi_torusN (t : Fin τ.rank → Kˣ) :
    monomialSubHom (τ := τ) (K := K) (torusN τ K t) = 1 := by
  have h : torusN τ K t ∈ (monomialSubHom (τ := τ) (K := K)).ker := by
    rw [monomialSubHom_ker, Subgroup.mem_subgroupOf, borelSub_inf_monomialSub]
    exact (torusCoordHom τ K t).2
  exact h

theorem conj_N_word {g : ↥(monomialSub τ K)} (l : List (Fin τ.rank))
    (hg : monomialSubHom (τ := τ) (K := K) g = wordW τ l) (t : Fin τ.rank → Kˣ) :
    g * torusN τ K t * g⁻¹ = torusN τ K (mact K (l.map (Rmat τ)).prod t) := by
  set w := (l.map (weylRep τ K)).prod with hw
  have hker : monomialSubHom (τ := τ) (K := K) (g * w⁻¹) = 1 := by
    rw [map_mul, map_inv, hg, hw, psi_wordProd, mul_inv_cancel]
  obtain ⟨u, hu⟩ := exists_torusN_of_psi_eq_one τ K hker
  have hg' : g = torusN τ K u * w := by
    rw [hu]; exact (inv_mul_cancel_right g w).symm
  have hcomm : torusN τ K u * (w * torusN τ K t * w⁻¹) * (torusN τ K u)⁻¹ =
      w * torusN τ K t * w⁻¹ := by
    rw [conj_word τ l t]
    exact mul_inv_eq_iff_eq_mul.2 (torusN_comm τ u _)
  calc g * torusN τ K t * g⁻¹
      = torusN τ K u * (w * torusN τ K t * w⁻¹) * (torusN τ K u)⁻¹ := by
        rw [hg']; group
    _ = _ := by rw [hcomm, conj_word τ l t]

end Torus

section Pair

variable {K : Type} [Field K] {r : ℕ}

theorem vecT_pow_three (c : Fin r → ℤ) (ω : Kˣ) (hω : orderOf ω = 3) : vecT c ω ^ 3 = 1 := by
  ext1 k
  simp only [vecT, Pi.pow_apply, Pi.one_apply]
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hω, pow_orderOf_eq_one,
    one_zpow]

theorem nine_dvd_of_vecT (H : Subgroup (Fin r → Kˣ)) (ω : Kˣ) (hω : orderOf ω = 3)
    (c₁ c₂ : Fin r → ℤ) (p₁ p₂ : Fin r) (h11 : c₁ p₁ = 1) (h12 : c₂ p₁ = 0) (h21 : c₁ p₂ = 0)
    (h22 : c₂ p₂ = 1) (m₁ : vecT c₁ ω ∈ H) (m₂ : vecT c₂ ω ∈ H) : 9 ∣ Nat.card H := by
  have hne : ω ≠ 1 := by
    intro h; rw [h, orderOf_one] at hω; omega
  have o₁ : orderOf (vecT c₁ ω) = 3 := by
    refine orderOf_eq_prime (vecT_pow_three c₁ ω hω) ?_
    intro h
    have := congrFun h p₁
    simp [vecT, h11] at this
    exact hne this
  refine nine_dvd_card_of_two H (fun a _ b _ => mul_comm a b) m₁ m₂ o₁ (vecT_pow_three c₂ ω hω) ?_
  rintro ⟨k, hk⟩
  have e1 := congrFun hk p₂
  simp [vecT, h21, h22] at e1
  exact hne e1.symm

end Pair

section Main

variable (τ : Tag) (K : Type) [Field K] [Finite K]

theorem eightyOne_dvd_of_pair (hinj : Function.Injective (torusN τ K))
    (lx ly : List (Fin τ.rank)) (s c : ↥(monomialSub τ K))
    (hs : monomialSubHom (τ := τ) (K := K) s = wordW τ lx)
    (hc : c ∈ Subgroup.centralizer ({s} : Set ↥(monomialSub τ K)))
    (hcy : monomialSubHom (τ := τ) (K := K) c = wordW τ ly)
    (ω : Kˣ) (hω : orderOf ω = 3) (c₁ c₂ : Fin τ.rank → ℤ) (p₁ p₂ : Fin τ.rank)
    (hf₁ : ∀ i, (3 : ℤ) ∣ ((lx.map (Rmat τ)).prod.mulVec c₁) i - c₁ i)
    (hf₂ : ∀ i, (3 : ℤ) ∣ ((lx.map (Rmat τ)).prod.mulVec c₂) i - c₂ i)
    (h11 : c₁ p₁ = 1) (h12 : c₂ p₁ = 0) (h21 : c₁ p₂ = 0) (h22 : c₂ p₂ = 1)
    (hQ : 9 ∣ Nat.card (Subgroup.closure ({wordW τ lx, wordW τ ly} : Set (WeylGroup τ)))) :
    81 ∣ Nat.card (Subgroup.centralizer ({s} : Set ↥(monomialSub τ K))) := by
  set ψ := monomialSubHom (τ := τ) (K := K) with hψ
  set C := Subgroup.centralizer ({s} : Set ↥(monomialSub τ K)) with hC
  set X := (lx.map (Rmat τ)).prod with hX
  refine eightyOne_dvd_of_ker_range ψ C ?_ ?_
  ·
    set Fix : Subgroup (Fin τ.rank → Kˣ) := (mactHom (K := K) (1 - X)).ker with hFix
    have hfixmem : ∀ t, t ∈ Fix ↔ mact K X t = t := by
      intro t
      rw [hFix, MonoidHom.mem_ker, mactHom_apply, mact_one_sub, mul_inv_eq_one, eq_comm]
    have hfixc : ∀ c' : Fin τ.rank → ℤ, (∀ i, (3 : ℤ) ∣ (X.mulVec c') i - c' i) →
        vecT c' ω ∈ Fix := by
      intro c' hc'
      rw [hfixmem, mact_vecT]
      exact vecT_eq_of_dvd _ _ ω hω hc'
    have h9 : 9 ∣ Nat.card Fix :=
      nine_dvd_of_vecT Fix ω hω c₁ c₂ p₁ p₂ h11 h12 h21 h22 (hfixc c₁ hf₁) (hfixc c₂ hf₂)
    have hle : Fix.map (torusN τ K) ≤ C ⊓ ψ.ker := by
      rintro _ ⟨t, ht, rfl⟩
      refine ⟨?_, psi_torusN τ K t⟩
      show torusN τ K t ∈ C
      rw [hC, Subgroup.mem_centralizer_singleton_iff]
      have := conj_N_word τ K lx hs t
      rw [← hX, (hfixmem t).1 ht] at this
      exact (mul_inv_eq_iff_eq_mul.1 this).symm
    rw [← Subgroup.card_map_of_injective hinj] at h9
    exact h9.trans (Subgroup.card_dvd_of_le hle)
  · have hle : Subgroup.closure ({wordW τ lx, wordW τ ly} : Set (WeylGroup τ)) ≤ C.map ψ := by
      rw [Subgroup.closure_le]
      rintro _ (rfl | rfl)
      · exact ⟨s, Subgroup.mem_centralizer_singleton_iff.2 rfl, hs⟩
      · exact ⟨c, hc, hcy⟩
    exact hQ.trans (Subgroup.card_dvd_of_le hle)

theorem exists_decomp {s gx : ↥(monomialSub τ K)}
    (h : monomialSubHom (τ := τ) (K := K) s = monomialSubHom (τ := τ) (K := K) gx) :
    ∃ t, s = torusN τ K t * gx := by
  have hker : monomialSubHom (τ := τ) (K := K) (s * gx⁻¹) = 1 := by
    rw [map_mul, map_inv, h, mul_inv_cancel]
  obtain ⟨t, ht⟩ := exists_torusN_of_psi_eq_one τ K hker
  exact ⟨t, by rw [ht]; exact (inv_mul_cancel_right s gx).symm⟩

theorem lift_centralizer_of_solve (lx ly : List (Fin τ.rank)) {s gx gy : ↥(monomialSub τ K)}
    (hgx : monomialSubHom (τ := τ) (K := K) gx = wordW τ lx)
    (hgy : monomialSubHom (τ := τ) (K := K) gy = wordW τ ly)
    (h u a : Fin τ.rank → Kˣ) (hs : s = torusN τ K h * gx)
    (hu : gy * gx * gy⁻¹ = torusN τ K u * gx)
    (ha : a * (mact K (lx.map (Rmat τ)).prod a)⁻¹ =
      h * (mact K (ly.map (Rmat τ)).prod h)⁻¹ * u⁻¹) :
    torusN τ K a * gy ∈ Subgroup.centralizer ({s} : Set ↥(monomialSub τ K)) ∧
      monomialSubHom (τ := τ) (K := K) (torusN τ K a * gy) = wordW τ ly := by
  refine ⟨lift_mem_centralizer (torusN τ K) (mactHom (K := K) (lx.map (Rmat τ)).prod)
    (mactHom (K := K) (ly.map (Rmat τ)).prod) gx gy s h u a hs
    (fun t => conj_N_word τ K lx hgx t) (fun t => conj_N_word τ K ly hgy t) hu ha, ?_⟩
  rw [map_mul, psi_torusN, one_mul, hgy]

theorem exists_comm_torus (hinj : Function.Injective (torusN τ K))
    {gx gy : ↥(monomialSub τ K)} (hx : gx ∈ What τ K) (hy : gy ∈ What τ K)
    (hcomm : monomialSubHom (τ := τ) (K := K) gy * monomialSubHom (τ := τ) (K := K) gx =
      monomialSubHom (τ := τ) (K := K) gx * monomialSubHom (τ := τ) (K := K) gy) :
    ∃ u : Fin τ.rank → Kˣ, u * u = 1 ∧ gy * gx * gy⁻¹ = torusN τ K u * gx := by
  set z := gy * gx * gy⁻¹ * gx⁻¹ with hz
  have hzW : z ∈ What τ K :=
    mul_mem (mul_mem (mul_mem hy hx) (inv_mem hy)) (inv_mem hx)
  have hz1 : monomialSubHom (τ := τ) (K := K) z = 1 := by
    rw [hz, map_mul, map_mul, map_mul, map_inv, map_inv, hcomm]
    group
  have hzZ : z ∈ Z0 τ K := What_ker_le_Z0 τ K hzW hz1
  obtain ⟨u, hu⟩ := Z0_le_range_torusN τ hzZ
  refine ⟨u, hinj ?_, ?_⟩
  · rw [map_mul, map_one, hu, ← sq]; exact Z0_sq τ K hzZ
  · rw [hu, hz]; group

theorem caseA (hinj : Function.Injective (torusN τ K))
    (lx ly : List (Fin τ.rank)) (s gx gy : ↥(monomialSub τ K))
    (hs : monomialSubHom (τ := τ) (K := K) s = wordW τ lx)
    (hgx : monomialSubHom (τ := τ) (K := K) gx = wordW τ lx)
    (hgy : monomialSubHom (τ := τ) (K := K) gy = wordW τ ly)
    (hcomm : gy * gx = gx * gy) (hgx3 : gx ^ 3 = 1) (hs3 : s ^ 3 = 1)
    (Φ Ψ : Matrix (Fin τ.rank) (Fin τ.rank) ℤ)
    (hid : 1 - (ly.map (Rmat τ)).prod =
      (1 - (lx.map (Rmat τ)).prod) * Φ + Ψ * (1 + (lx.map (Rmat τ)).prod +
        (lx.map (Rmat τ)).prod * (lx.map (Rmat τ)).prod))
    (ω : Kˣ) (hω : orderOf ω = 3) (c₁ c₂ : Fin τ.rank → ℤ) (p₁ p₂ : Fin τ.rank)
    (hf₁ : ∀ i, (3 : ℤ) ∣ ((lx.map (Rmat τ)).prod.mulVec c₁) i - c₁ i)
    (hf₂ : ∀ i, (3 : ℤ) ∣ ((lx.map (Rmat τ)).prod.mulVec c₂) i - c₂ i)
    (h11 : c₁ p₁ = 1) (h12 : c₂ p₁ = 0) (h21 : c₁ p₂ = 0) (h22 : c₂ p₂ = 1)
    (hQ : 9 ∣ Nat.card (Subgroup.closure ({wordW τ lx, wordW τ ly} : Set (WeylGroup τ)))) :
    81 ∣ Nat.card (Subgroup.centralizer ({s} : Set ↥(monomialSub τ K))) := by
  set X := (lx.map (Rmat τ)).prod with hX
  set Y := (ly.map (Rmat τ)).prod with hY
  obtain ⟨h, hsh⟩ := exists_decomp τ K (hs.trans hgx.symm)
  have hcube := cube_of_conj (torusN τ K) (mactHom (K := K) X) gx h
    (fun t => conj_N_word τ K lx hgx t) hgx3
  rw [← hsh, hs3, ← map_one (torusN τ K)] at hcube
  have hN : mact K (1 + X + X * X) h = 1 := by
    have := hinj hcube
    rw [mact_add, mact_add, mact_one, mact_mul]
    simpa [mactHom_apply, mul_assoc] using this.symm
  have ha : mact K Φ h * (mact K X (mact K Φ h))⁻¹ =
      h * (mact K Y h)⁻¹ * (1 : Fin τ.rank → Kˣ)⁻¹ := by
    have h1 : mact K (1 - Y) h = h * (mact K Y h)⁻¹ := mact_one_sub Y h
    have h2 : mact K (1 - X) (mact K Φ h) = mact K Φ h * (mact K X (mact K Φ h))⁻¹ :=
      mact_one_sub X _
    rw [← h2, inv_one, mul_one, ← h1, hid, mact_add, mact_mul Ψ, hN, mact_one_vec, mul_one,
      mact_mul]
  have hu : gy * gx * gy⁻¹ = torusN τ K 1 * gx := by
    rw [map_one, one_mul, mul_inv_eq_iff_eq_mul, hcomm]
  obtain ⟨hc, hcy⟩ := lift_centralizer_of_solve τ K lx ly hgx hgy h 1 _ hsh hu ha
  exact eightyOne_dvd_of_pair τ K hinj lx ly s _ hs hc hcy ω hω c₁ c₂ p₁ p₂ hf₁ hf₂ h11 h12 h21
    h22 hQ

theorem solve_group {n : ℕ} (X : Matrix (Fin τ.rank) (Fin τ.rank) ℤ)
    (Y : Fin n → Matrix (Fin τ.rank) (Fin τ.rank) ℤ) (Ξ : Matrix (Fin τ.rank) (Fin τ.rank) ℤ)
    (hΞ : (1 - X) * Ξ = (3 : ℤ) • 1) (u : Fin n → (Fin τ.rank → Kˣ)) (hu : ∀ i, u i * u i = 1)
    (hsolve : ∀ c : Fin τ.rank → ℤ, ∃ i : Fin n, ∃ d : Fin τ.rank → ℤ,
      (1 - X).mulVec d = (1 - Y i).mulVec c) (h : Fin τ.rank → Kˣ) :
    ∃ i : Fin n, ∃ a : Fin τ.rank → Kˣ,
      a * (mact K X a)⁻¹ = h * (mact K (Y i) h)⁻¹ * (u i)⁻¹ := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hc : ∀ k, ∃ m : ℤ, g ^ m = h k := fun k => Subgroup.mem_zpowers_iff.1 (hg (h k))
  choose c hc using hc
  have hh : h = vecT c g := funext fun k => (hc k).symm
  obtain ⟨i, d, hd⟩ := hsolve c
  refine ⟨i, vecT d g * mact K Ξ (u i)⁻¹, ?_⟩
  have e1 : mact K (1 - X) (vecT d g) = h * (mact K (Y i) h)⁻¹ := by
    rw [mact_vecT, hd, ← mact_vecT, ← hh, mact_one_sub]
  have e2 : mact K (1 - X) (mact K Ξ (u i)⁻¹) = (u i)⁻¹ := by
    rw [← mact_mul, hΞ, mact_smul_one]
    have h2 : (u i)⁻¹ * (u i)⁻¹ = 1 := by rw [← mul_inv, hu, inv_one]
    calc (u i)⁻¹ ^ (3 : ℤ) = (u i)⁻¹ * ((u i)⁻¹ * (u i)⁻¹) := by group
      _ = (u i)⁻¹ := by rw [h2, mul_one]
  rw [← mact_one_sub, mact_mul_apply, e1, e2]

theorem caseB (hinj : Function.Injective (torusN τ K)) {n : ℕ}
    (lx : List (Fin τ.rank)) (ly : Fin n → List (Fin τ.rank)) (s gx : ↥(monomialSub τ K))
    (hs : monomialSubHom (τ := τ) (K := K) s = wordW τ lx)
    (hgx : monomialSubHom (τ := τ) (K := K) gx = wordW τ lx) (hgxW : gx ∈ What τ K)
    (hcomm : ∀ i, wordW τ (ly i) * wordW τ lx = wordW τ lx * wordW τ (ly i))
    (Ξ : Matrix (Fin τ.rank) (Fin τ.rank) ℤ)
    (hΞ : (1 - (lx.map (Rmat τ)).prod) * Ξ = (3 : ℤ) • 1)
    (hsolve : ∀ c : Fin τ.rank → ℤ, ∃ i : Fin n, ∃ d : Fin τ.rank → ℤ,
      (1 - (lx.map (Rmat τ)).prod).mulVec d = (1 - ((ly i).map (Rmat τ)).prod).mulVec c)
    (ω : Kˣ) (hω : orderOf ω = 3) (c₁ c₂ : Fin τ.rank → ℤ) (p₁ p₂ : Fin τ.rank)
    (hf₁ : ∀ i, (3 : ℤ) ∣ ((lx.map (Rmat τ)).prod.mulVec c₁) i - c₁ i)
    (hf₂ : ∀ i, (3 : ℤ) ∣ ((lx.map (Rmat τ)).prod.mulVec c₂) i - c₂ i)
    (h11 : c₁ p₁ = 1) (h12 : c₂ p₁ = 0) (h21 : c₁ p₂ = 0) (h22 : c₂ p₂ = 1)
    (hQ : ∀ i, 9 ∣ Nat.card (Subgroup.closure
      ({wordW τ lx, wordW τ (ly i)} : Set (WeylGroup τ)))) :
    81 ∣ Nat.card (Subgroup.centralizer ({s} : Set ↥(monomialSub τ K))) := by
  obtain ⟨h, hsh⟩ := exists_decomp τ K (hs.trans hgx.symm)
  have hg : ∀ i, ∃ gy ∈ What τ K,
      monomialSubHom (τ := τ) (K := K) gy = wordW τ (ly i) := fun i => What_surj τ K _
  choose gy hgyW hgy using hg
  have hu : ∀ i, ∃ u : Fin τ.rank → Kˣ, u * u = 1 ∧
      gy i * gx * (gy i)⁻¹ = torusN τ K u * gx := fun i =>
    exists_comm_torus τ K hinj hgxW (hgyW i) (by rw [hgy, hgx]; exact hcomm i)
  choose u hu1 hu2 using hu
  obtain ⟨i, a, ha⟩ := solve_group τ K _ (fun i => ((ly i).map (Rmat τ)).prod) Ξ hΞ u hu1
    hsolve h
  obtain ⟨hc, hcy⟩ := lift_centralizer_of_solve τ K lx (ly i) hgx (hgy i) h (u i) a hsh (hu2 i) ha
  exact eightyOne_dvd_of_pair τ K hinj lx (ly i) s _ hs hc hcy ω hω c₁ c₂ p₁ p₂ hf₁ hf₂ h11 h12
    h21 h22 (hQ i)

end Main

end CFSG.HardMathSupport.Curtis.UnitaryLevi

end
