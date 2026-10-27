module

public import CFSG.LocalAnalysis.AGLEmbedding.NongenerationTransfer
import CFSG.LocalAnalysis.AGLEmbedding.LinTwoBorelAux

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.PreuniquenessRankFour.Helpers CFSG.RankThreeCoreUniqueness.Helpers

theorem le_of_le_sup_of_isPGroup_of_coprime {G : Type*} [Group G] {p : ℕ} [Fact p.Prime]
    {X Y N : Subgroup G} (hX : IsPGroup p X) (hN : p.Coprime (Nat.card N))
    (hNY : N ≤ Subgroup.normalizer (Y : Set G)) (hXYN : X ≤ Y ⊔ N) : X ≤ Y := by
  intro e he
  have hx : e ∈ ((Y ⊔ N : Subgroup G) : Set G) := hXYN he
  rw [Subgroup.coe_mul_of_right_le_normalizer_left Y N hNY] at hx
  obtain ⟨y, hy, t, ht, rfl⟩ := hx
  obtain ⟨k, hk⟩ := hX ⟨y * t, he⟩
  have hk' : (y * t) ^ (p ^ k) = 1 := congrArg Subtype.val hk
  have key : ∀ m : ℕ, ∃ y' ∈ Y, (y * t) ^ m = y' * t ^ m := by
    intro m
    induction m with
    | zero => exact ⟨1, Y.one_mem, by simp⟩
    | succ m ih =>
      obtain ⟨y', hy', hm⟩ := ih
      refine ⟨y' * (t ^ m * y * (t ^ m)⁻¹), Y.mul_mem hy' ?_, ?_⟩
      · exact (Subgroup.mem_normalizer_iff.1 (hNY (N.pow_mem ht m)) y).1 hy
      · rw [pow_succ, hm, pow_succ]
        group
  obtain ⟨y', hy', hyp⟩ := key (p ^ k)
  have htm : t ^ (p ^ k) ∈ Y := by
    have h1 : y' * t ^ (p ^ k) = 1 := by rw [← hyp]; exact hk'
    rw [eq_inv_of_mul_eq_one_right h1]
    exact Y.inv_mem hy'
  have hT1 : t ^ Nat.card N = 1 :=
    congrArg Subtype.val (pow_card_eq_one' (G := N) (x := (⟨t, ht⟩ : N)))
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 (hN.pow_left k)
  have htY : t ∈ Y := by
    have e1 : t = (t ^ (p ^ k)) ^ a * (t ^ Nat.card N) ^ b := by
      calc t = t ^ (1 : ℤ) := (zpow_one t).symm
        _ = t ^ (a * ((p ^ k : ℕ) : ℤ) + b * (Nat.card N : ℤ)) := by rw [hab]
        _ = (t ^ (p ^ k)) ^ a * (t ^ Nat.card N) ^ b := by
          rw [zpow_add, mul_comm a, mul_comm b, zpow_mul, zpow_mul, zpow_natCast, zpow_natCast]
    rw [e1, hT1, one_zpow, mul_one]
    exact Y.zpow_mem htm a
  exact Y.mul_mem hy htY

theorem eq_bot_of_commutator_eq_self_of_le {Y : Type*} [Group Y] {W Z : Subgroup Y} (hWZ : W ≤ Z)
    (hZ : Group.IsSolvable Z) (hW : ⁅W, W⁆ = W) : W = ⊥ := by
  have : Group.IsSolvable W :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hWZ)
      (Subgroup.inclusion_injective hWZ)
  by_contra hne
  have : Nontrivial W := (Subgroup.nontrivial_iff_ne_bot W).mpr hne
  have htop : commutator W = ⊤ := by
    apply Subgroup.map_injective W.subtype_injective
    rw [Subgroup.map_subtype_commutator, hW, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  exact (Group.IsSolvable.commutator_lt_top_of_nontrivial W).ne htop

theorem exists_torus_of_map_eq {Q : Type*} [Group Q] [Finite Q] {p : ℕ} (hp : p.Prime)
    (O : Subgroup Q) [O.Normal] (hO : p.Coprime (Nat.card O)) {A B : Subgroup Q}
    (hA : IsPGroup p A) (hOB : O ≤ B) {F : Type*} [Field F] (ψ : Multiplicative F →* Q ⧸ O)
    (hψ : Function.Injective ψ) (hψA : ψ.range = A.map (QuotientGroup.mk' O))
    (hc : ∀ μ : Fˣ, ∃ c ∈ B.map (QuotientGroup.mk' O), ∀ a : Multiplicative F,
      c * ψ a * c⁻¹ = ψ (Multiplicative.ofAdd ((μ : F) ^ 2 * Multiplicative.toAdd a))) :
    ∃ φ : Multiplicative F ≃* A, ∀ μ : Fˣ, ∃ t ∈ B, ∀ a : Multiplicative F,
      t * (φ a : Q) * t⁻¹ = φ (Multiplicative.ofAdd ((μ : F) ^ 2 * Multiplicative.toAdd a)) := by
  let g : A →* Q ⧸ O := (QuotientGroup.mk' O).comp A.subtype
  have hg : ∀ x : A, g x = QuotientGroup.mk' O (x : Q) := fun x => rfl
  have hginj : Function.Injective g := by
    intro x y hxy
    have hmem : ((x * y⁻¹ : A) : Q) ∈ A ⊓ O := by
      refine ⟨(x * y⁻¹).2, ?_⟩
      have h1 : QuotientGroup.mk' O ((x * y⁻¹ : A) : Q) = 1 := by
        rw [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, ← hg, ← hg, hxy,
          mul_inv_cancel]
      rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    rw [inf_eq_bot_of_isPGroup hp hA hO, Subgroup.mem_bot] at hmem
    exact mul_inv_eq_one.mp (Subtype.ext hmem)
  have hgr : ψ.range = g.range := by
    rw [hψA, MonoidHom.range_comp, Subgroup.range_subtype]
  let φ : Multiplicative F ≃* A := (MonoidHom.ofInjective hψ).trans
    ((MulEquiv.subgroupCongr hgr).trans (MonoidHom.ofInjective hginj).symm)
  have hφ : ∀ a, g (φ a) = ψ a := by
    intro a
    change g ((MonoidHom.ofInjective hginj).symm
      (MulEquiv.subgroupCongr hgr (MonoidHom.ofInjective hψ a))) = ψ a
    rw [MonoidHom.apply_ofInjective_symm, MulEquiv.subgroupCongr_apply,
      MonoidHom.ofInjective_apply]
  refine ⟨φ, fun μ => ?_⟩
  obtain ⟨_, ⟨b, hb, rfl⟩, hcψ⟩ := hc μ
  have hbN : QuotientGroup.mk' O b ∈
      Subgroup.normalizer ((A.map (QuotientGroup.mk' O) : Subgroup (Q ⧸ O)) : Set (Q ⧸ O)) :=
    hψA ▸ mem_normalizer_range_of_torus ψ μ.ne_zero hcψ
  obtain ⟨o, ho, t, ht, rfl⟩ :=
    Subgroup.mem_sup_of_normal_left.mp (comap_normalizer_map_le_sup hp O hO hA hbN)
  have ho1 : QuotientGroup.mk' O o = 1 := (QuotientGroup.eq_one_iff o).mpr ho
  have hot : QuotientGroup.mk' O (o * t) = QuotientGroup.mk' O t := by
    rw [map_mul, ho1, one_mul]
  refine ⟨t, by simpa using B.mul_mem (B.inv_mem (hOB ho)) hb, fun a => ?_⟩
  have hmem : t * (φ a : Q) * t⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp ht _).mp (φ a).2
  have heq : (⟨t * (φ a : Q) * t⁻¹, hmem⟩ : A) =
      φ (Multiplicative.ofAdd ((μ : F) ^ 2 * Multiplicative.toAdd a)) := by
    apply hginj
    rw [hφ, ← hcψ, ← hφ a, hg, hg, hot, map_mul, map_mul, map_inv]
  exact congrArg Subtype.val heq

section Quotient

variable {G : Type} [Group G] [Finite G] {p : ℕ} {H : Subgroup G}

theorem mem_glbPrimeCore_iff_mk_eq_one (h : H) :
    (h : G) ∈ GLBPrimeCore p H ↔ QuotientGroup.mk' (primeComplementCore (G := H) p) h = 1 := by
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, glbPrimeCore_eq_primeComplementCoreOf]
  exact Subgroup.mem_map_iff_mem H.subtype_injective

theorem le_glbPrimeCore_of_map_eq_bot {Y : Subgroup G} (hYH : Y ≤ H)
    (hY : (Y.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) = ⊥) :
    Y ≤ GLBPrimeCore p H := by
  intro y hy
  refine (mem_glbPrimeCore_iff_mk_eq_one ⟨y, hYH hy⟩).mpr ?_
  rw [← Subgroup.mem_bot, ← hY]
  exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hy)

theorem le_sup_glbPrimeCore_of_map_le {X Y : Subgroup G} (hYH : Y ≤ H)
    (hYX : (Y.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) ≤
      (X.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p))) :
    Y ≤ X ⊔ GLBPrimeCore p H := by
  intro y hy
  obtain ⟨x, hx, hxy⟩ := hYX (Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hy) :
    QuotientGroup.mk' (primeComplementCore (G := H) p) ⟨y, hYH hy⟩ ∈ _)
  have hk : ((x⁻¹ * ⟨y, hYH hy⟩ : H) : G) ∈ GLBPrimeCore p H := by
    rw [mem_glbPrimeCore_iff_mk_eq_one, map_mul, map_inv, hxy, inv_mul_cancel]
  have hy' : y = (x : G) * ((x⁻¹ * ⟨y, hYH hy⟩ : H) : G) := by simp
  rw [hy']
  exact Subgroup.mul_mem_sup (Subgroup.mem_subgroupOf.mp hx) hk

omit [Finite G] in
theorem map_mk_le_normalizer_map_mk {A Y : Subgroup G} (hAY : A ≤ Subgroup.normalizer (Y : Set G)) :
    (A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) ≤
      Subgroup.normalizer (((Y.subgroupOf H).map
        (QuotientGroup.mk' (primeComplementCore (G := H) p)) : Subgroup _) : Set _) :=
  (Subgroup.map_mono ((Subgroup.subgroupOf_mono H hAY).trans
    (Subgroup.le_normalizer_comap H.subtype))).trans (Subgroup.le_normalizer_map _)

theorem isPGroup_map_of_forall_pow_mem {Y : Subgroup G}
    (hY : ∀ y ∈ Y, ∃ k : ℕ, y ^ p ^ k ∈ GLBPrimeCore p H) :
    IsPGroup p ((Y.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p))) := by
  rintro ⟨_, y, hy, rfl⟩
  obtain ⟨k, hk⟩ := hY y (Subgroup.mem_subgroupOf.mp hy)
  refine ⟨k, Subtype.ext ?_⟩
  change (QuotientGroup.mk' (primeComplementCore (G := H) p) y) ^ p ^ k = 1
  rw [← map_pow, ← mem_glbPrimeCore_iff_mk_eq_one, Subgroup.coe_pow]
  exact hk

omit [Finite G] in
theorem commutator_map_eq_self {Y : Subgroup G} (hYH : Y ≤ H) (hY : ⁅Y, Y⁆ = Y) :
    ⁅(Y.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)),
      (Y.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p))⁆ =
      (Y.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) := by
  have h : ⁅Y.subgroupOf H, Y.subgroupOf H⁆ = Y.subgroupOf H := by
    apply Subgroup.map_injective H.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hYH, hY]
  rw [← Subgroup.map_commutator, h]

theorem le_glbPrimeCore_or_le_of_forall [Fact p.Prime] {M X Y : Subgroup G}
    (hNM : GLBPrimeCore p H ≤ M) (hXH : X ≤ H) (hX : IsPGroup p X)
    (hD : ∀ W : Subgroup (H ⧸ primeComplementCore (G := H) p),
      W ≤ ((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) →
      ((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) ≤
        Subgroup.normalizer (W : Set (H ⧸ primeComplementCore (G := H) p)) →
      W = ⊥ ∨ (X.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) ≤ W)
    (hY : Y ≤ H ⊓ M) (hYN : H ⊓ M ≤ Subgroup.normalizer (Y : Set G)) :
    Y ≤ GLBPrimeCore p H ∨ X ≤ Y := by
  rcases hD _ (Subgroup.map_mono (Subgroup.subgroupOf_mono H hY)) (map_mk_le_normalizer_map_mk hYN)
    with hbot | hle
  · exact Or.inl (le_glbPrimeCore_of_map_eq_bot (hY.trans inf_le_left) hbot)
  · right
    have hON : primeComplementCore (G := H) p ≤
        Subgroup.normalizer ((Y.subgroupOf H : Subgroup H) : Set H) := by
      intro o ho
      have hoN : (o : G) ∈ GLBPrimeCore p H :=
        (mem_glbPrimeCore_iff_mk_eq_one o).mpr ((QuotientGroup.eq_one_iff o).mpr ho)
      exact Subgroup.le_normalizer_comap H.subtype (hYN ⟨o.2, hNM hoN⟩)
    have hXY : X.subgroupOf H ≤ Y.subgroupOf H := by
      refine le_of_le_sup_of_isPGroup_of_coprime hX.comap_subtype (primeComplementCore_coprime p)
        hON ?_
      rw [sup_comm, ← QuotientGroup.comap_map_mk']
      exact Subgroup.map_le_iff_le_comap.mp hle
    intro x hx
    exact Subgroup.mem_subgroupOf.mp
      (hXY (Subgroup.mem_subgroupOf.mpr hx : (⟨x, hXH hx⟩ : H) ∈ X.subgroupOf H))

theorem le_sup_glbPrimeCore_of_forall {M X Y : Subgroup G}
    (hP : ∀ W : Subgroup (H ⧸ primeComplementCore (G := H) p),
      W ≤ ((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) →
      ((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) ≤
        Subgroup.normalizer (W : Set (H ⧸ primeComplementCore (G := H) p)) → IsPGroup p W →
      W ≤ (X.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)))
    (hY : Y ≤ H ⊓ M) (hYN : H ⊓ M ≤ Subgroup.normalizer (Y : Set G))
    (hYp : ∀ y ∈ Y, ∃ k : ℕ, y ^ p ^ k ∈ GLBPrimeCore p H) :
    Y ≤ X ⊔ GLBPrimeCore p H :=
  le_sup_glbPrimeCore_of_map_le (hY.trans inf_le_left)
    (hP _ (Subgroup.map_mono (Subgroup.subgroupOf_mono H hY)) (map_mk_le_normalizer_map_mk hYN)
      (isPGroup_map_of_forall_pow_mem hYp))

theorem le_glbPrimeCore_of_perfect {M L : Subgroup G}
    (hS : Group.IsSolvable
      (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p))))
    (hL : L ≤ H ⊓ M) (hLL : ⁅L, L⁆ = L) : L ≤ GLBPrimeCore p H :=
  le_glbPrimeCore_of_map_eq_bot (hL.trans inf_le_left)
    (eq_bot_of_commutator_eq_self_of_le (Subgroup.map_mono (Subgroup.subgroupOf_mono H hL)) hS
      (commutator_map_eq_self (hL.trans inf_le_left) hLL))

theorem pRank_inf_le_of_pRank_top_le (hp : p.Prime) {M : Subgroup G} {n : ℕ}
    (h : pRank p (⊤ : Subgroup (H ⧸ primeComplementCore (G := H) p)) ≤ n) :
    pRank p (H ⊓ M) ≤ n := by
  have h1 := pRank_map_mk_eq_pRank_map_subtype hp (primeComplementCore (G := H) p)
    (primeComplementCore_coprime p) ⊤
  rw [Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _),
    ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h1
  exact (pRank_mono p hp inf_le_left).trans (h1 ▸ h)

theorem exists_torus_of_map_subgroupOf_eq [Fact p.Prime] {B X : Subgroup G} (hXH : X ≤ H)
    (hX : IsPGroup p X) (hNB : GLBPrimeCore p H ≤ B) {F : Type*} [Field F]
    (ψ : Multiplicative F →* H ⧸ primeComplementCore (G := H) p) (hψ : Function.Injective ψ)
    (hψX : ψ.range = (X.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)))
    (hc : ∀ μ : Fˣ,
      ∃ c ∈ (B.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)),
        ∀ a : Multiplicative F,
          c * ψ a * c⁻¹ = ψ (Multiplicative.ofAdd ((μ : F) ^ 2 * Multiplicative.toAdd a))) :
    ∃ φ : Multiplicative F ≃* X, ∀ μ : Fˣ, ∃ t ∈ B, ∀ a : Multiplicative F,
      t * (φ a : G) * t⁻¹ = φ (Multiplicative.ofAdd ((μ : F) ^ 2 * Multiplicative.toAdd a)) := by
  have hOB : primeComplementCore (G := H) p ≤ B.subgroupOf H := fun o ho =>
    Subgroup.mem_subgroupOf.mpr
      (hNB ((mem_glbPrimeCore_iff_mk_eq_one o).mpr ((QuotientGroup.eq_one_iff o).mpr ho)))
  obtain ⟨φ, hφ⟩ := exists_torus_of_map_eq Fact.out _ (primeComplementCore_coprime p)
    hX.comap_subtype hOB ψ hψ hψX hc
  refine ⟨φ.trans (Subgroup.subgroupOfEquivOfLe hXH), fun μ => ?_⟩
  obtain ⟨t, ht, htφ⟩ := hφ μ
  exact ⟨t, Subgroup.mem_subgroupOf.mp ht, fun a => congrArg Subtype.val (htφ a)⟩

end Quotient

end CFSG.AGLEmbedding
