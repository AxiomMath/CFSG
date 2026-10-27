module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.D3ZL4

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley Matrix
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Lang.D4Three
  CFSG.RankThree.PartTwo.Census.Carrier.D4Even
open scoped Pointwise



section Groups

variable {K : Type} [Field K] [Finite K]

local notation "ρ" => simpleRootSL2 Tag.D4 K

@[expose] def Uk (K : Type) [Field K] (k : Fin Tag.D4.rank) : Subgroup (ModGL Tag.D4 K) :=
  (xUnitHom Tag.D4 K k).range

@[expose] def Lk (K : Type) [Field K] (k : Fin Tag.D4.rank) : Subgroup (ModGL Tag.D4 K) :=
  (simpleRootSL2 Tag.D4 K k).range

theorem mem_Uk {k : Fin Tag.D4.rank} {x : ModGL Tag.D4 K} :
    x ∈ Uk K k ↔ ∃ c : K, xUnit Tag.D4 K k c = x :=
  ⟨fun ⟨c, hc⟩ => ⟨c.toAdd, hc⟩, fun ⟨c, hc⟩ => ⟨Multiplicative.ofAdd c, hc⟩⟩

theorem xUnit_mem_Uk (k : Fin Tag.D4.rank) (c : K) : xUnit Tag.D4 K k c ∈ Uk K k :=
  mem_Uk.2 ⟨c, rfl⟩

theorem mem_Lk {k : Fin Tag.D4.rank} {x : ModGL Tag.D4 K} :
    x ∈ Lk K k ↔ ∃ X : SL2 K, ρ k X = x := Iff.rfl

theorem Uk_le_Lk (k : Fin Tag.D4.rank) : Uk K k ≤ Lk K k := by
  intro x hx
  obtain ⟨c, rfl⟩ := mem_Uk.1 hx
  exact ⟨uSL c, simpleRootSL2_uSL k c⟩

theorem card_Uk (k : Fin Tag.D4.rank) : Nat.card (Uk K k) = Nat.card K := by
  have hinj : Function.Injective (xUnitHom Tag.D4 K k) := by
    intro c d h
    exact Multiplicative.toAdd.injective (xUnit_inj_d4 k h)
  calc Nat.card (Uk K k) = Nat.card (Set.range (xUnitHom Tag.D4 K k)) := rfl
    _ = Nat.card (Multiplicative K) := Nat.card_range_of_injective hinj
    _ = Nat.card K := rfl

end Groups

section Norm

variable {K : Type} [Field K] [Finite K]

local notation "ρ" => simpleRootSL2 Tag.D4 K

theorem commute_xUnit_outer {j k : Fin Tag.D4.rank} (hj : j ∈ ({0, 1, 3} : Set (Fin Tag.D4.rank)))
    (hk : k ∈ ({0, 1, 3} : Set (Fin Tag.D4.rank))) (hjk : j ≠ k) (c d : K) :
    Commute (xUnit Tag.D4 K j c) (xUnit Tag.D4 K k d) := by
  have := commute_rho_outer (K := K) hj hk hjk (uSL c) (uSL d)
  rwa [simpleRootSL2_uSL, simpleRootSL2_uSL] at this

theorem eq_or_outer {J : Set (Fin Tag.D4.rank)}
    (hJ : J = {2} ∨ J = ({0, 1, 3} : Set (Fin Tag.D4.rank))) {j k : Fin Tag.D4.rank} (hj : j ∈ J)
    (hk : k ∈ J) : j = k ∨ (j ≠ k ∧ j ∈ ({0, 1, 3} : Set (Fin Tag.D4.rank)) ∧
      k ∈ ({0, 1, 3} : Set (Fin Tag.D4.rank))) := by
  rcases hJ with rfl | rfl
  · left; rw [Set.mem_singleton_iff.1 hj, Set.mem_singleton_iff.1 hk]
  · by_cases h : j = k
    · exact Or.inl h
    · exact Or.inr ⟨h, hj, hk⟩

theorem torus_le_normalizer_Uk (k : Fin Tag.D4.rank) :
    torusGroup Tag.D4 K ≤ Subgroup.normalizer (Uk K k : Set (ModGL Tag.D4 K)) := fun t ht => by
  haveI := finite_modGL (τ := Tag.D4) (K := K)
  obtain ⟨b, rfl⟩ := torusGroup_le_range ht
  refine mem_normalizer_of_forall_conj_mem (Uk K k) fun u hu => ?_
  obtain ⟨c, rfl⟩ := mem_Uk.1 hu
  change rootDiagUnit Tag.D4 b * xUnit Tag.D4 K k c * (rootDiagUnit Tag.D4 b)⁻¹ ∈ Uk K k
  rw [(root_diagonal_conjugation Tag.D4 K b).1 k c]
  exact xUnit_mem_Uk k _

theorem torus_le_normalizer_Lk (k : Fin Tag.D4.rank) :
    torusGroup Tag.D4 K ≤ Subgroup.normalizer (Lk K k : Set (ModGL Tag.D4 K)) := fun t ht => by
  haveI := finite_modGL (τ := Tag.D4) (K := K)
  obtain ⟨b, rfl⟩ := torusGroup_le_range ht
  refine mem_normalizer_of_forall_conj_mem (Lk K k) fun u hu => ?_
  obtain ⟨X, rfl⟩ := mem_Lk.1 hu
  change rootDiagUnit Tag.D4 b * ρ k X * (rootDiagUnit Tag.D4 b)⁻¹ ∈ Lk K k
  rw [torus_conj_rho]
  exact ⟨_, rfl⟩

theorem closure_le_normalizer_Uk {J : Set (Fin Tag.D4.rank)}
    (hJ : J = {2} ∨ J = ({0, 1, 3} : Set (Fin Tag.D4.rank))) {k : Fin Tag.D4.rank} (hk : k ∈ J) :
    Subgroup.closure {x | ∃ j ∈ J, ∃ c : K, x = xUnit Tag.D4 K j c} ≤
      Subgroup.normalizer (Uk K k : Set (ModGL Tag.D4 K)) := by
  haveI := finite_modGL (τ := Tag.D4) (K := K)
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨j, hj, c, rfl⟩
  rcases eq_or_outer hJ hj hk with rfl | ⟨hjk, hjo, hko⟩
  · exact Subgroup.le_normalizer (xUnit_mem_Uk j c)
  · refine mem_normalizer_of_forall_conj_mem (Uk K k) fun u hu => ?_
    obtain ⟨d, rfl⟩ := mem_Uk.1 hu
    rw [(commute_xUnit_outer hjo hko hjk c d).eq, mul_inv_cancel_right]
    exact xUnit_mem_Uk k d

theorem levi_le_normalizer_Lk {J : Set (Fin Tag.D4.rank)}
    (hJ : J = {2} ∨ J = ({0, 1, 3} : Set (Fin Tag.D4.rank))) {k : Fin Tag.D4.rank} (hk : k ∈ J) :
    parabolicLevi Tag.D4 K J ≤ Subgroup.normalizer (Lk K k : Set (ModGL Tag.D4 K)) := by
  haveI := finite_modGL (τ := Tag.D4) (K := K)
  refine sup_le (torus_le_normalizer_Lk k) ((Subgroup.closure_le _).2 ?_)
  rintro _ ⟨j, hj, c, rfl | rfl⟩
  · rcases eq_or_outer hJ hj hk with rfl | ⟨hjk, hjo, hko⟩
    · exact Subgroup.le_normalizer (Uk_le_Lk j (xUnit_mem_Uk j c))
    · refine mem_normalizer_of_forall_conj_mem (Lk K k) fun u hu => ?_
      obtain ⟨X, rfl⟩ := mem_Lk.1 hu
      have := commute_rho_outer (K := K) hjo hko hjk (uSL c) X
      rw [simpleRootSL2_uSL] at this
      rw [this.eq, mul_inv_cancel_right]
      exact hu
  · rcases eq_or_outer hJ hj hk with rfl | ⟨hjk, hjo, hko⟩
    · exact Subgroup.le_normalizer ⟨vSL c, simpleRootSL2_vSL j c⟩
    · refine mem_normalizer_of_forall_conj_mem (Lk K k) fun u hu => ?_
      obtain ⟨X, rfl⟩ := mem_Lk.1 hu
      have := commute_rho_outer (K := K) hjo hko hjk (vSL c) X
      rw [simpleRootSL2_vSL] at this
      rw [this.eq, mul_inv_cancel_right]
      exact hu

theorem proj_borel_normalizer_Uk {J : Set (Fin Tag.D4.rank)}
    (hJ : J = {2} ∨ J = ({0, 1, 3} : Set (Fin Tag.D4.rank))) {g : ModGL Tag.D4 K}
    (hg : g ∈ borelGroup Tag.D4 K) {k : Fin Tag.D4.rank} (hk : k ∈ J) :
    (semiDirect_levi (K := K) J).proj g ∈ Subgroup.normalizer (Uk K k : Set (ModGL Tag.D4 K)) := by
  have hg' : g ∈ (parabolicRadical Tag.D4 K J : Set (ModGL Tag.D4 K)) *
      ((torusGroup Tag.D4 K : Set (ModGL Tag.D4 K)) *
        (parabolicLeviUnipotent Tag.D4 K J : Set (ModGL Tag.D4 K))) := by
    rw [← borelGroup_eq_mul_parabolic J]; exact hg
  obtain ⟨q, hq, tv, ⟨t, ht, v, hv, rfl⟩, rfl⟩ := hg'
  have htM : t ∈ parabolicLevi Tag.D4 K J := torusGroup_le_parabolicLevi J ht
  have hvM : v ∈ parabolicLevi Tag.D4 K J := parabolicLeviUnipotent_le_parabolicLevi J hv
  have hP : q * (t * v) ∈ parabolicSubgroup Tag.D4 K J :=
    (semiDirect_levi (K := K) J).Q_le hq |> fun hq' =>
      mul_mem hq' ((semiDirect_levi (K := K) J).M_le (mul_mem htM hvM))
  rw [(semiDirect_levi (K := K) J).proj_eq hP hq (mul_mem htM hvM) rfl]
  exact mul_mem (torus_le_normalizer_Uk k ht) (closure_le_normalizer_Uk hJ hk (leviUnip_le hJ hv))

end Norm

section Bar

variable {K : Type} [Field K] [Finite K]

local notation "ρ" => simpleRootSL2 Tag.D4 K

theorem phi_xUnit (g : ModGL Tag.D4 K) (a : Fin Tag.D4.rank → Kˣ) (σ : K ≃+* K) (ε : ℕ)
    (k : Fin Tag.D4.rank) : ∃ e : K, ∀ c : K, phiG g a σ ε (xUnit Tag.D4 K k c) =
      g * xUnit Tag.D4 K ((d4Rho ^ ε) k) (e * σ c) * g⁻¹ := by
  obtain ⟨e, he⟩ := exists_d4F_pinnedX (K := K) a σ ε
  refine ⟨e (Pi.single k 1), fun c => ?_⟩
  rw [phiG_apply, ← pinnedX_single, he _ (isRoot_single Tag.D4 k), permLattice_single, pinnedX_single]

theorem phi_yUnit (g : ModGL Tag.D4 K) (a : Fin Tag.D4.rank → Kˣ) (σ : K ≃+* K) (ε : ℕ)
    (k : Fin Tag.D4.rank) : ∃ e : K, ∀ c : K, phiG g a σ ε (yUnit Tag.D4 K k c) =
      g * yUnit Tag.D4 K ((d4Rho ^ ε) k) (e * σ c) * g⁻¹ := by
  obtain ⟨e, he⟩ := exists_d4F_pinnedX (K := K) a σ ε
  refine ⟨e (-Pi.single k 1), fun c => ?_⟩
  have h1 : permLattice (d4Rho ^ ε) (-Pi.single k 1 : Fin Tag.D4.rank → ℤ) =
      -Pi.single ((d4Rho ^ ε) k) 1 := by
    rw [← permLattice_single]; rfl
  rw [phiG_apply, ← pinnedX_neg_single, he _ (isRoot_neg_single Tag.D4 k), h1, pinnedX_neg_single]

theorem Lk_le_levi {J : Set (Fin Tag.D4.rank)} {k : Fin Tag.D4.rank} (hk : k ∈ J) :
    Lk K k ≤ parabolicLevi Tag.D4 K J := by
  unfold Lk
  rw [range_simpleRootSL2]
  refine (Subgroup.closure_le _).2 ?_
  rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
  · exact xUnit_mem_parabolicLevi hk c
  · exact yUnit_mem_parabolicLevi hk c

variable {J : Set (Fin Tag.D4.rank)} {g : ModGL Tag.D4 K} {a : Fin Tag.D4.rank → Kˣ}
  {σ : K ≃+* K} {ε : ℕ}

theorem bar_xUnit_mem (hJ : J = {2} ∨ J = ({0, 1, 3} : Set (Fin Tag.D4.rank)))
    (hg : g ∈ borelGroup Tag.D4 K) (hJρ : ∀ i, i ∈ J ↔ (d4Rho ^ ε) i ∈ J) {k : Fin Tag.D4.rank}
    (hk : k ∈ J) (c : K) :
    (semiDirect_levi (K := K) J).bar (phiG g a σ ε) (xUnit Tag.D4 K k c) ∈
      Uk K ((d4Rho ^ ε) k) := by
  obtain ⟨e, he⟩ := phi_xUnit g a σ ε k
  have hk' : (d4Rho ^ ε) k ∈ J := (hJρ k).1 hk
  have hgP : g ∈ parabolicSubgroup Tag.D4 K J := borelGroup_le_parabolicSubgroup J hg
  have hxM := xUnit_mem_parabolicLevi (K := K) hk' (e * σ c)
  unfold IsSemiDirect.bar
  rw [he c, (semiDirect_levi (K := K) J).proj_conj hgP ((semiDirect_levi (K := K) J).M_le hxM),
    (semiDirect_levi (K := K) J).proj_of_mem_M hxM]
  exact (Subgroup.mem_normalizer_iff.1 (proj_borel_normalizer_Uk hJ hg hk') _).1
    (xUnit_mem_Uk _ _)

theorem bar_yUnit_mem (hJ : J = {2} ∨ J = ({0, 1, 3} : Set (Fin Tag.D4.rank)))
    (hg : g ∈ borelGroup Tag.D4 K) (hJρ : ∀ i, i ∈ J ↔ (d4Rho ^ ε) i ∈ J) {k : Fin Tag.D4.rank}
    (hk : k ∈ J) (c : K) :
    (semiDirect_levi (K := K) J).bar (phiG g a σ ε) (yUnit Tag.D4 K k c) ∈
      Lk K ((d4Rho ^ ε) k) := by
  obtain ⟨e, he⟩ := phi_yUnit g a σ ε k
  have hk' : (d4Rho ^ ε) k ∈ J := (hJρ k).1 hk
  have hgP : g ∈ parabolicSubgroup Tag.D4 K J := borelGroup_le_parabolicSubgroup J hg
  have hyM := yUnit_mem_parabolicLevi (K := K) hk' (e * σ c)
  unfold IsSemiDirect.bar
  rw [he c, (semiDirect_levi (K := K) J).proj_conj hgP ((semiDirect_levi (K := K) J).M_le hyM),
    (semiDirect_levi (K := K) J).proj_of_mem_M hyM]
  have hpM : (semiDirect_levi (K := K) J).proj g ∈ parabolicLevi Tag.D4 K J :=
    (semiDirect_levi (K := K) J).proj_mem hgP
  exact (Subgroup.mem_normalizer_iff.1 (levi_le_normalizer_Lk hJ hk' hpM) _).1
    ⟨vSL _, simpleRootSL2_vSL _ _⟩

theorem bar_Uk_le (hJ : J = {2} ∨ J = ({0, 1, 3} : Set (Fin Tag.D4.rank)))
    (hg : g ∈ borelGroup Tag.D4 K) (hJρ : ∀ i, i ∈ J ↔ (d4Rho ^ ε) i ∈ J) {k : Fin Tag.D4.rank}
    (hk : k ∈ J) {x : ModGL Tag.D4 K} (hx : x ∈ Uk K k) :
    (semiDirect_levi (K := K) J).bar (phiG g a σ ε) x ∈ Uk K ((d4Rho ^ ε) k) := by
  obtain ⟨c, rfl⟩ := mem_Uk.1 hx
  exact bar_xUnit_mem hJ hg hJρ hk c

theorem bar_Lk_le (hJ : J = {2} ∨ J = ({0, 1, 3} : Set (Fin Tag.D4.rank)))
    (hg : g ∈ borelGroup Tag.D4 K) (hJρ : ∀ i, i ∈ J ↔ (d4Rho ^ ε) i ∈ J)
    (hφP : ∀ x ∈ parabolicSubgroup Tag.D4 K J, phiG g a σ ε x ∈ parabolicSubgroup Tag.D4 K J)
    {k : Fin Tag.D4.rank} (hk : k ∈ J) {x : ModGL Tag.D4 K} (hx : x ∈ Lk K k) :
    (semiDirect_levi (K := K) J).bar (phiG g a σ ε) x ∈ Lk K ((d4Rho ^ ε) k) := by
  obtain ⟨X, rfl⟩ := mem_Lk.1 hx
  clear hx
  have hcl : Subgroup.closure (Set.range (uSL (K := K)) ∪ Set.range (vSL (K := K))) = ⊤ :=
    CFSG.LocalAnalysis.ComponentInitial.sl2_closure_upper_lower
  have htop : X ∈ Subgroup.closure (Set.range (uSL (K := K)) ∪ Set.range (vSL (K := K))) := by
    rw [hcl]; trivial
  have hLP : ∀ Y : SL2 K, ρ k Y ∈ parabolicSubgroup Tag.D4 K J := fun Y =>
    (semiDirect_levi (K := K) J).M_le (Lk_le_levi hk ⟨Y, rfl⟩)
  induction htop using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with ⟨c, rfl⟩ | ⟨c, rfl⟩
    · rw [simpleRootSL2_uSL]; exact Uk_le_Lk _ (bar_xUnit_mem hJ hg hJρ hk c)
    · rw [simpleRootSL2_vSL]; exact bar_yUnit_mem hJ hg hJρ hk c
  | one => rw [map_one, (semiDirect_levi (K := K) J).bar_one]; exact one_mem _
  | mul x y _ _ hx hy =>
    rw [map_mul, (semiDirect_levi (K := K) J).bar_mul _ hφP (hLP x) (hLP y)]
    exact mul_mem hx hy
  | inv x _ hx =>
    rw [map_inv, (semiDirect_levi (K := K) J).bar_inv _ hφP (hLP x)]
    exact inv_mem hx

theorem bar_injOn (hφP : ∀ x ∈ parabolicSubgroup Tag.D4 K J, phiG g a σ ε x ∈ parabolicSubgroup Tag.D4 K J)
    (hφQ : ∀ q ∈ parabolicRadical Tag.D4 K J, phiG g a σ ε q ∈ parabolicRadical Tag.D4 K J)
    (hφ3 : ∀ m ∈ parabolicLevi Tag.D4 K J,
      phiG g a σ ε (phiG g a σ ε (phiG g a σ ε m)) = m)
    {x y : ModGL Tag.D4 K} (hx : x ∈ parabolicLevi Tag.D4 K J) (hy : y ∈ parabolicLevi Tag.D4 K J)
    (h : (semiDirect_levi (K := K) J).bar (phiG g a σ ε) x =
      (semiDirect_levi (K := K) J).bar (phiG g a σ ε) y) : x = y := by
  have hS := semiDirect_levi (K := K) J
  have hbm : ∀ z ∈ parabolicLevi Tag.D4 K J, hS.bar (phiG g a σ ε) z ∈ parabolicLevi Tag.D4 K J :=
    fun z hz => hS.bar_mem _ hφP (hS.M_le hz)
  rw [← hS.bar_bar_bar _ hφP hφQ hφ3 hx, ← hS.bar_bar_bar _ hφP hφQ hφ3 hy, h]

theorem bar_Uk_surj (hJ : J = {2} ∨ J = ({0, 1, 3} : Set (Fin Tag.D4.rank)))
    (hg : g ∈ borelGroup Tag.D4 K) (hJρ : ∀ i, i ∈ J ↔ (d4Rho ^ ε) i ∈ J)
    (hφP : ∀ x ∈ parabolicSubgroup Tag.D4 K J, phiG g a σ ε x ∈ parabolicSubgroup Tag.D4 K J)
    (hφQ : ∀ q ∈ parabolicRadical Tag.D4 K J, phiG g a σ ε q ∈ parabolicRadical Tag.D4 K J)
    (hφ3 : ∀ m ∈ parabolicLevi Tag.D4 K J, phiG g a σ ε (phiG g a σ ε (phiG g a σ ε m)) = m)
    {k : Fin Tag.D4.rank} (hk : k ∈ J) :
    ∀ y ∈ Uk K ((d4Rho ^ ε) k), ∃ x ∈ Uk K k,
      (semiDirect_levi (K := K) J).bar (phiG g a σ ε) x = y := by
  haveI := finite_modGL (τ := Tag.D4) (K := K)
  let f : Uk K k → Uk K ((d4Rho ^ ε) k) := fun x =>
    ⟨(semiDirect_levi (K := K) J).bar (phiG g a σ ε) x, bar_Uk_le hJ hg hJρ hk x.2⟩
  have hinj : Function.Injective f := fun x x' hxx' =>
    Subtype.ext (bar_injOn hφP hφQ hφ3 (Lk_le_levi hk (Uk_le_Lk _ x.2))
      (Lk_le_levi hk (Uk_le_Lk _ x'.2)) (congrArg Subtype.val hxx'))
  have hcard : Nat.card (Uk K ((d4Rho ^ ε) k)) ≤ Nat.card (Uk K k) := by
    rw [card_Uk, card_Uk]
  intro y hy
  obtain ⟨x, hx⟩ := (hinj.bijective_of_nat_card_le hcard).2 ⟨y, hy⟩
  exact ⟨x, x.2, congrArg Subtype.val hx⟩

end Bar

end CFSG.LocalAnalysis.GLTheoremA
