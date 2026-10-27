module

public import CFSG.LieType.Seitz.Defs
public import CFSG.GroupTheory.HyperplaneGeneration
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.LieType.SeitzGeneration.QuasiHigh

open CFSG.LieType.Seitz
open scoped commutatorElement

variable {K : Type*} [Group K]

theorem apply_mem_center (f : MulAut K) {z : K} (hz : z ∈ Subgroup.center K) :
    f z ∈ Subgroup.center K := by
  rw [← Subgroup.map_center_eq f]
  exact ⟨z, hz, rfl⟩

noncomputable def quotAut (f : MulAut K) : MulAut (K ⧸ Subgroup.center K) :=
  QuotientGroup.congr (Subgroup.center K) (Subgroup.center K) f (Subgroup.map_center_eq f)

@[simp]
theorem quotAut_mk (f : MulAut K) (x : K) :
    quotAut f (x : K ⧸ Subgroup.center K) = ((f x : K) : K ⧸ Subgroup.center K) :=
  QuotientGroup.congr_mk _ _ _ _ x

theorem quotAut_one (s : K ⧸ Subgroup.center K) : quotAut (1 : MulAut K) s = s := by
  induction s using QuotientGroup.induction_on with
  | H x => rw [quotAut_mk]; rfl

theorem quotAut_mul (f g : MulAut K) (s : K ⧸ Subgroup.center K) :
    quotAut (f * g) s = quotAut f (quotAut g s) := by
  induction s using QuotientGroup.induction_on with
  | H x => rw [quotAut_mk, quotAut_mk, quotAut_mk]; rfl

theorem quotAut_conj (k : K) (s : K ⧸ Subgroup.center K) :
    quotAut (MulAut.conj k) s =
      (k : K ⧸ Subgroup.center K) * s * (k : K ⧸ Subgroup.center K)⁻¹ := by
  induction s using QuotientGroup.induction_on with
  | H x => rw [quotAut_mk, MulAut.conj_apply]; rfl

def centerTorsion (K : Type*) [Group K] (M : ℕ) : Subgroup K where
  carrier := {z | z ∈ Subgroup.center K ∧ z ^ M = 1}
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    have hc : Commute a b := (Subgroup.mem_center_iff.1 ha b).symm
    exact ⟨Subgroup.mul_mem _ ha hb, by rw [hc.mul_pow, ha', hb', one_mul]⟩
  one_mem' := ⟨Subgroup.one_mem _, one_pow M⟩
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    exact ⟨Subgroup.inv_mem _ ha, by rw [inv_pow, ha', inv_one]⟩

theorem mem_centerTorsion {M : ℕ} {z : K} :
    z ∈ centerTorsion K M ↔ z ∈ Subgroup.center K ∧ z ^ M = 1 := Iff.rfl

theorem not_dvd_card_centerTorsion [Finite K] {p : ℕ} [Fact p.Prime] {M : ℕ} (hM : ¬ p ∣ M) :
    ¬ p ∣ Nat.card (centerTorsion K M) := by
  intro hd
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' p hd
  apply hM
  rw [← hz]
  refine orderOf_dvd_of_pow_eq_one (Subtype.ext ?_)
  simpa using (mem_centerTorsion.1 z.2).2

theorem exists_basePoint [Finite K] {p : ℕ} [hp : Fact p.Prime] {x : K} {m : ℕ} (hm : ¬ p ∣ m)
    (hxm : x ^ m ∈ Subgroup.center K) :
    ∃ M : ℕ, ¬ p ∣ M ∧ ∃ y₀ : K, x⁻¹ * y₀ ∈ Subgroup.center K ∧ y₀ ^ M = 1 := by
  set Z := Subgroup.center K with hZ
  set N := Nat.card Z with hN
  have hN0 : N ≠ 0 := Nat.card_pos.ne'
  set a := N.factorization p with ha
  set N' := N / p ^ a with hN'
  have hNN : p ^ a * N' = N := Nat.ordProj_mul_ordCompl_eq_self N p
  have hN'p : ¬ p ∣ N' := Nat.not_dvd_ordCompl hp.out hN0
  have hco : Nat.Coprime m (p ^ a) :=
    Nat.Coprime.pow_right a (Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hp.out).2 hm))
  obtain ⟨k, hk1, hk0⟩ := Nat.chineseRemainder hco 1 0
  refine ⟨m * N', fun h => ((Nat.Prime.dvd_mul hp.out).1 h).elim hm hN'p, x ^ k, ?_, ?_⟩
  · have h1 : ((m : ℕ) : ℤ) ∣ ((1 : ℕ) : ℤ) - (k : ℤ) := Nat.modEq_iff_dvd.1 hk1
    obtain ⟨t, ht⟩ := h1
    have e : x⁻¹ * x ^ k = (x ^ m) ^ (-t) := by
      rw [← zpow_natCast x k, ← zpow_neg_one x, ← zpow_add, ← zpow_natCast x m, ← zpow_mul]
      congr 1
      push_cast at ht
      linear_combination -ht
    rw [e]
    exact Subgroup.zpow_mem _ hxm _
  · obtain ⟨j, hj⟩ := Nat.modEq_zero_iff_dvd.1 hk0
    have hxN : (x ^ m) ^ N = 1 := by
      have h1 : (⟨x ^ m, hxm⟩ : Z) ^ N = 1 := pow_card_eq_one'
      have h2 := congrArg Subtype.val h1
      rwa [Subgroup.coe_pow, Subgroup.coe_one] at h2
    rw [← pow_mul, hj]
    calc x ^ (p ^ a * j * (m * N')) = ((x ^ m) ^ N) ^ j := by
          rw [← pow_mul, ← pow_mul, ← hNN]
          congr 1
          ring
      _ = 1 := by rw [hxN, one_pow]

theorem exists_fixed_mul_center [Finite K] {p : ℕ} [hp : Fact p.Prime]
    {F : Subgroup (MulAut K)} (hF : IsPGroup p F) {x : K}
    (hx : ∀ f ∈ F, x⁻¹ * f x ∈ Subgroup.center K)
    (hc : ¬ p ∣ Nat.card (Subgroup.center K) ∨
      ∃ m : ℕ, ¬ p ∣ m ∧ x ^ m ∈ Subgroup.center K) :
    ∃ y : K, x⁻¹ * y ∈ Subgroup.center K ∧ ∀ f ∈ F, f y = y := by
  classical
  set Z := Subgroup.center K with hZ
  obtain ⟨M, y₀, hy₀, hy₀M, hMp⟩ : ∃ (M : ℕ) (y₀ : K), x⁻¹ * y₀ ∈ Z ∧ y₀ ^ M = 1 ∧
      ¬ p ∣ Nat.card (centerTorsion K M) := by
    rcases hc with hZp | ⟨m, hm, hxm⟩
    · refine ⟨0, x, by rw [inv_mul_cancel]; exact Z.one_mem, pow_zero x, ?_⟩
      have h0 : centerTorsion K 0 = Z := by
        ext z
        exact ⟨fun h => h.1, fun h => ⟨h, pow_zero z⟩⟩
      rw [h0]
      exact hZp
    · obtain ⟨M, hMp, y₀, hy₀, hy₀M⟩ := exists_basePoint hm hxm
      exact ⟨M, y₀, hy₀, hy₀M, not_dvd_card_centerTorsion hMp⟩
  set T : Set K := {y | x⁻¹ * y ∈ Z ∧ y ^ M = 1} with hT
  have hTF : ∀ f ∈ F, ∀ y ∈ T, f y ∈ T := by
    rintro f hf y ⟨hy1, hy2⟩
    refine ⟨?_, by rw [← map_pow, hy2, map_one]⟩
    have h1 : x⁻¹ * f y = (x⁻¹ * f x) * f (x⁻¹ * y) := by
      rw [map_mul, map_inv]
      group
    rw [h1]
    exact Z.mul_mem (hx f hf) (apply_mem_center f hy1)
  letI : MulAction F T :=
    { smul := fun f y => ⟨(f : MulAut K) y, hTF f f.2 y y.2⟩
      one_smul := fun y => Subtype.ext rfl
      mul_smul := fun f g y => Subtype.ext rfl }
  have hcen : ∀ {z : K}, z ∈ Z → Commute y₀ z := fun hz => (Subgroup.mem_center_iff.1 hz y₀)
  have hcard : Nat.card T = Nat.card (centerTorsion K M) := by
    refine Nat.card_congr
      { toFun := fun y => ⟨y₀⁻¹ * y, ?_, ?_⟩
        invFun := fun z => ⟨y₀ * z, ?_, ?_⟩
        left_inv := fun y => Subtype.ext (by simp)
        right_inv := fun z => Subtype.ext (by simp) }
    · have e : y₀⁻¹ * (y : K) = (x⁻¹ * y₀)⁻¹ * (x⁻¹ * y) := by group
      rw [e]
      exact Z.mul_mem (Z.inv_mem hy₀) y.2.1
    · have hz : y₀⁻¹ * (y : K) ∈ Z := by
        have e : y₀⁻¹ * (y : K) = (x⁻¹ * y₀)⁻¹ * (x⁻¹ * y) := by group
        rw [e]
        exact Z.mul_mem (Z.inv_mem hy₀) y.2.1
      have h1 : (y : K) ^ M = y₀ ^ M * (y₀⁻¹ * y) ^ M := by
        rw [← (hcen hz).mul_pow, mul_inv_cancel_left]
      rw [y.2.2, hy₀M, one_mul] at h1
      exact h1.symm
    · have e : x⁻¹ * (y₀ * z) = (x⁻¹ * y₀) * z := by group
      rw [e]
      exact Z.mul_mem hy₀ z.2.1
    · rw [(hcen z.2.1).mul_pow, hy₀M, z.2.2, one_mul]
  have hT0 : ¬ p ∣ Nat.card T := hcard ▸ hMp
  obtain ⟨⟨t, ht1, ht2⟩, ht⟩ := hF.nonempty_fixed_point_of_prime_not_dvd_card T hT0
  refine ⟨t, ht1, fun f hf => ?_⟩
  exact congrArg Subtype.val ((MulAction.mem_fixedPoints.1 ht) ⟨f, hf⟩)

theorem eq_top_of_sup_center_eq_top (hperf : commutator K = ⊤) {H : Subgroup K}
    (h : H ⊔ Subgroup.center K = ⊤) : H = ⊤ := by
  have hdec : ∀ g : K, ∃ a ∈ H, ∃ z ∈ Subgroup.center K, g = a * z := by
    intro g
    have hg : g ∈ Subgroup.center K ⊔ H := by
      rw [sup_comm, h]
      exact Subgroup.mem_top g
    obtain ⟨z, hz, a, ha, hza⟩ := Subgroup.mem_sup_of_normal_left.1 hg
    refine ⟨a, ha, z, hz, ?_⟩
    rw [← hza]
    exact (Subgroup.mem_center_iff.1 hz a).symm
  have hcomm : commutator K ≤ H := by
    rw [commutator_def, Subgroup.commutator_le]
    intro g₁ _ g₂ _
    obtain ⟨a₁, ha₁, z₁, hz₁, rfl⟩ := hdec g₁
    obtain ⟨a₂, ha₂, z₂, hz₂, rfl⟩ := hdec g₂
    have c1 := Subgroup.mem_center_iff.mp hz₁
    have c2 := Subgroup.mem_center_iff.mp hz₂
    have e : a₁ * z₁ * (a₂ * z₂) * (a₁ * z₁)⁻¹ * (a₂ * z₂)⁻¹ = a₁ * a₂ * a₁⁻¹ * a₂⁻¹ := by
      calc a₁ * z₁ * (a₂ * z₂) * (a₁ * z₁)⁻¹ * (a₂ * z₂)⁻¹
          = a₁ * (z₁ * (a₂ * z₂)) * z₁⁻¹ * a₁⁻¹ * z₂⁻¹ * a₂⁻¹ := by group
        _ = a₁ * (a₂ * z₂ * z₁) * z₁⁻¹ * a₁⁻¹ * z₂⁻¹ * a₂⁻¹ := by rw [← c1 (a₂ * z₂)]
        _ = a₁ * a₂ * (z₂ * a₁⁻¹) * z₂⁻¹ * a₂⁻¹ := by group
        _ = a₁ * a₂ * (a₁⁻¹ * z₂) * z₂⁻¹ * a₂⁻¹ := by rw [← c2 a₁⁻¹]
        _ = a₁ * a₂ * a₁⁻¹ * a₂⁻¹ := by group
    rw [commutatorElement_def, e]
    exact H.mul_mem (H.mul_mem (H.mul_mem ha₁ ha₂) (H.inv_mem ha₁)) (H.inv_mem ha₂)
  rw [eq_top_iff, ← hperf]
  exact hcomm

theorem closure_sup_center_eq_top_of_image {T : Set K}
    (h : (⊤ : Subgroup (K ⧸ Subgroup.center K)) ≤
      Subgroup.closure ((QuotientGroup.mk' (Subgroup.center K)) '' T)) :
    Subgroup.closure T ⊔ Subgroup.center K = ⊤ := by
  have h1 : (Subgroup.closure T).map (QuotientGroup.mk' (Subgroup.center K)) = ⊤ := by
    rw [MonoidHom.map_closure]
    exact top_le_iff.1 h
  have h2 := congrArg (Subgroup.comap (QuotientGroup.mk' (Subgroup.center K))) h1
  rwa [Subgroup.comap_map_eq, QuotientGroup.ker_mk', Subgroup.comap_top] at h2

theorem seitzHyperGamma_eq_top_of_lift [Finite K] (hperf : commutator K = ⊤) {p : ℕ}
    [Fact p.Prime] {E : Subgroup (MulAut K)} (hE : IsPGroup p E) (T : Set K)
    (hT : ∀ x ∈ T, ∃ F ≤ E, F.relIndex E = p ∧ ∀ f ∈ F, x⁻¹ * f x ∈ Subgroup.center K)
    (hTc : ∀ x ∈ T, ¬ p ∣ Nat.card (Subgroup.center K) ∨
      ∃ m : ℕ, ¬ p ∣ m ∧ x ^ m ∈ Subgroup.center K)
    (hgen : Subgroup.closure T ⊔ Subgroup.center K = ⊤) :
    seitzHyperGamma p E = ⊤ := by
  apply eq_top_of_sup_center_eq_top hperf
  rw [eq_top_iff, ← hgen]
  refine sup_le ?_ le_sup_right
  rw [Subgroup.closure_le]
  intro x hx
  obtain ⟨F, hFE, hFi, hFx⟩ := hT x hx
  obtain ⟨y, hyx, hy⟩ := exists_fixed_mul_center (hE.to_le hFE) hFx (hTc x hx)
  have hyΓ : y ∈ seitzHyperGamma p E :=
    (le_iSup₂_of_le (f := fun (F : Subgroup (MulAut K)) (_ : F ≤ E ∧ F.relIndex E = p) =>
      fixedPoints F) F ⟨hFE, hFi⟩ le_rfl) (mem_fixedPoints.2 hy)
  have e : x = y * (x⁻¹ * y)⁻¹ := by group
  rw [SetLike.mem_coe, e]
  exact Subgroup.mul_mem_sup hyΓ (Subgroup.inv_mem _ hyx)

theorem seitzHyperGamma_eq_top_of_quot [Finite K] (hperf : commutator K = ⊤) {p : ℕ}
    [Fact p.Prime] {E : Subgroup (MulAut K)} (hE : IsPGroup p E)
    (hgen : (⊤ : Subgroup (K ⧸ Subgroup.center K)) ≤ Subgroup.closure
      {s : K ⧸ Subgroup.center K | (¬ p ∣ Nat.card (Subgroup.center K) ∨
        ∃ m : ℕ, ¬ p ∣ m ∧ s ^ m = 1) ∧
        ∃ F ≤ E, F.relIndex E = p ∧ ∀ f ∈ F, quotAut f s = s}) :
    seitzHyperGamma p E = ⊤ := by
  set S : Set (K ⧸ Subgroup.center K) := {s | (¬ p ∣ Nat.card (Subgroup.center K) ∨
    ∃ m : ℕ, ¬ p ∣ m ∧ s ^ m = 1) ∧ ∃ F ≤ E, F.relIndex E = p ∧ ∀ f ∈ F, quotAut f s = s}
    with hS
  refine seitzHyperGamma_eq_top_of_lift hperf hE
    {x : K | (x : K ⧸ Subgroup.center K) ∈ S} ?_ ?_ ?_
  · rintro x ⟨-, F, hFE, hFi, hFx⟩
    refine ⟨F, hFE, hFi, fun f hf => ?_⟩
    have h1 := hFx f hf
    rw [quotAut_mk] at h1
    exact QuotientGroup.eq.1 h1.symm
  · rintro x ⟨hc, -⟩
    rcases hc with hc | ⟨m, hm, hxm⟩
    · exact Or.inl hc
    · refine Or.inr ⟨m, hm, ?_⟩
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, hxm]
  · refine closure_sup_center_eq_top_of_image (hgen.trans (Subgroup.closure_mono ?_))
    intro s hs
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective s
    exact ⟨x, hs, rfl⟩

theorem seitzHyperGamma_eq_top_of_coprime_center [Finite K] (hperf : commutator K = ⊤) {p : ℕ}
    [Fact p.Prime] (hZ : ¬ p ∣ Nat.card (Subgroup.center K)) {E : Subgroup (MulAut K)}
    (hE : IsPGroup p E)
    (hgen : (⊤ : Subgroup (K ⧸ Subgroup.center K)) ≤ Subgroup.closure
      {s : K ⧸ Subgroup.center K | ∃ F ≤ E, F.relIndex E = p ∧ ∀ f ∈ F, quotAut f s = s}) :
    seitzHyperGamma p E = ⊤ :=
  seitzHyperGamma_eq_top_of_quot hperf hE (hgen.trans (Subgroup.closure_mono fun _ hs =>
    ⟨Or.inl hZ, hs⟩))

theorem apply_commutatorElement_of_fixed {f : MulAut K} {x y : K}
    (hx : quotAut f (x : K ⧸ Subgroup.center K) = (x : K ⧸ Subgroup.center K))
    (hy : quotAut f (y : K ⧸ Subgroup.center K) = (y : K ⧸ Subgroup.center K)) :
    f ⁅x, y⁆ = ⁅x, y⁆ := by
  rw [quotAut_mk] at hx hy
  obtain ⟨z, hz, hxz⟩ : ∃ z ∈ Subgroup.center K, f x = x * z :=
    ⟨x⁻¹ * f x, QuotientGroup.eq.1 hx.symm, by group⟩
  obtain ⟨w, hw, hyw⟩ : ∃ w ∈ Subgroup.center K, f y = y * w :=
    ⟨y⁻¹ * f y, QuotientGroup.eq.1 hy.symm, by group⟩
  have c1 := Subgroup.mem_center_iff.mp hz
  have c2 := Subgroup.mem_center_iff.mp hw
  rw [map_commutatorElement, hxz, hyw, commutatorElement_def, commutatorElement_def]
  calc x * z * (y * w) * (x * z)⁻¹ * (y * w)⁻¹
      = x * (z * (y * w)) * z⁻¹ * x⁻¹ * w⁻¹ * y⁻¹ := by group
    _ = x * (y * w * z) * z⁻¹ * x⁻¹ * w⁻¹ * y⁻¹ := by rw [← c1 (y * w)]
    _ = x * y * (w * x⁻¹) * w⁻¹ * y⁻¹ := by group
    _ = x * y * (x⁻¹ * w) * w⁻¹ * y⁻¹ := by rw [← c2 x⁻¹]
    _ = x * y * x⁻¹ * y⁻¹ := by group

theorem le_map_fixedPoints_of_perfect {F : Subgroup (MulAut K)}
    {H : Subgroup (K ⧸ Subgroup.center K)} (hH : ⁅H, H⁆ = H)
    (hfix : ∀ f ∈ F, ∀ s ∈ H, quotAut f s = s) :
    H ≤ (fixedPoints F).map (QuotientGroup.mk' (Subgroup.center K)) := by
  set P := H.comap (QuotientGroup.mk' (Subgroup.center K)) with hP
  have hPH : P.map (QuotientGroup.mk' (Subgroup.center K)) = H :=
    Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) H
  have hle : ⁅P, P⁆ ≤ fixedPoints F := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    exact mem_fixedPoints.2 fun f hf => apply_commutatorElement_of_fixed (hfix f hf _ hx)
      (hfix f hf _ hy)
  calc H = ⁅H, H⁆ := hH.symm
    _ = (⁅P, P⁆).map (QuotientGroup.mk' (Subgroup.center K)) := by
        rw [Subgroup.map_commutator, hPH]
    _ ≤ (fixedPoints F).map (QuotientGroup.mk' (Subgroup.center K)) := Subgroup.map_mono hle

theorem seitzHyperGamma_eq_top_of_perfect (hperf : commutator K = ⊤) {p : ℕ}
    {E : Subgroup (MulAut K)} (𝓗 : Set (Subgroup (K ⧸ Subgroup.center K)))
    (hH : ∀ H ∈ 𝓗, ⁅H, H⁆ = H)
    (hfix : ∀ H ∈ 𝓗, ∃ F ≤ E, F.relIndex E = p ∧ ∀ f ∈ F, ∀ s ∈ H, quotAut f s = s)
    (hgen : ⨆ H ∈ 𝓗, H = ⊤) : seitzHyperGamma p E = ⊤ := by
  apply eq_top_of_sup_center_eq_top hperf
  have hmap : (seitzHyperGamma p E).map (QuotientGroup.mk' (Subgroup.center K)) = ⊤ := by
    rw [eq_top_iff, ← hgen]
    refine iSup₂_le fun H hH' => ?_
    obtain ⟨F, hFE, hFrel, hF⟩ := hfix H hH'
    refine (le_map_fixedPoints_of_perfect (hH H hH') hF).trans (Subgroup.map_mono ?_)
    exact le_iSup₂_of_le (f := fun (F : Subgroup (MulAut K)) (_ : F ≤ E ∧ F.relIndex E = p) =>
      fixedPoints F) F ⟨hFE, hFrel⟩ le_rfl
  have h2 := congrArg (Subgroup.comap (QuotientGroup.mk' (Subgroup.center K))) hmap
  rwa [Subgroup.comap_map_eq, QuotientGroup.ker_mk', Subgroup.comap_top] at h2

theorem isElementaryAbelian_of_isElemAbelian {G : Type*} [Group G] {p : ℕ} {E : Subgroup G}
    (hE : CFSG.Open.IsElemAbelian p E) : CFSG.IsElementaryAbelian p E :=
  { toIsMulCommutative := hE.1
    exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x =>
      Subtype.ext (by rw [Subgroup.coe_pow, hE.2 x x.2, Subgroup.coe_one]) }

theorem isPGroup_of_isElemAbelian {G : Type*} [Group G] {p : ℕ} {E : Subgroup G}
    (hE : CFSG.Open.IsElemAbelian p E) : IsPGroup p E :=
  fun x => ⟨1, Subtype.ext (by rw [pow_one, Subgroup.coe_pow, hE.2 x x.2, Subgroup.coe_one])⟩

theorem le_closure_of_p'Subgroup [Finite K] {p : ℕ} [Fact p.Prime] {E : Subgroup (MulAut K)}
    (hE : CFSG.Open.IsElemAbelian p E) (hE1 : E ≠ ⊥) {H : Subgroup (K ⧸ Subgroup.center K)}
    (hp' : ¬ p ∣ Nat.card H) (hstab : ∀ f ∈ E, ∀ s ∈ H, quotAut f s ∈ H) :
    H ≤ Subgroup.closure {s : K ⧸ Subgroup.center K | (∃ m : ℕ, ¬ p ∣ m ∧ s ^ m = 1) ∧
      ∃ F ≤ E, F.relIndex E = p ∧ ∀ f ∈ F, quotAut f s = s} := by
  classical
  haveI : CFSG.IsElementaryAbelian p E := isElementaryAbelian_of_isElemAbelian hE
  haveI : Nontrivial E := (Subgroup.nontrivial_iff_ne_bot E).2 hE1
  letI : MulDistribMulAction E H :=
    { smul := fun f s => ⟨quotAut (f : MulAut K) s, hstab f f.2 s s.2⟩
      one_smul := fun s => Subtype.ext (quotAut_one (s : K ⧸ Subgroup.center K))
      mul_smul := fun f g s => Subtype.ext (quotAut_mul (f : MulAut K) g s)
      smul_mul := fun f s t => Subtype.ext
        (map_mul (quotAut (f : MulAut K)) (s : K ⧸ Subgroup.center K) t)
      smul_one := fun f => Subtype.ext (map_one (quotAut (f : MulAut K))) }
  have hgen := CFSG.SolvableHall.coprime_hyperplane_generation (p := p) (A := E) (H := H) hp'
  intro s hs
  have hmem : (⟨s, hs⟩ : H) ∈ ⨆ (B : Subgroup E) (_ : B.index = p),
      CFSG.fixedPointSubgroup B H := by
    rw [hgen]
    exact Subgroup.mem_top _
  have hle : (⨆ (B : Subgroup E) (_ : B.index = p), CFSG.fixedPointSubgroup B H) ≤
      (Subgroup.closure {s : K ⧸ Subgroup.center K | (∃ m : ℕ, ¬ p ∣ m ∧ s ^ m = 1) ∧
        ∃ F ≤ E, F.relIndex E = p ∧ ∀ f ∈ F, quotAut f s = s}).comap H.subtype := by
    refine iSup₂_le fun B hB => fun t ht => ?_
    refine Subgroup.subset_closure ⟨⟨Nat.card H, hp', ?_⟩, B.map E.subtype,
      Subgroup.map_subtype_le B, ?_, ?_⟩
    · have h1 : t ^ Nat.card H = 1 := pow_card_eq_one'
      have h2 := congrArg Subtype.val h1
      rwa [Subgroup.coe_pow, Subgroup.coe_one] at h2
    · rw [Subgroup.relIndex, Subgroup.subgroupOf,
        Subgroup.comap_map_eq_self_of_injective E.subtype_injective]
      exact hB
    · rintro _ ⟨b, hb, rfl⟩
      exact congrArg Subtype.val (ht ⟨b, hb⟩)
  exact hle hmem

theorem seitzHyperGamma_eq_top_of_p'Subgroups [Finite K] (hperf : commutator K = ⊤) {p : ℕ}
    [Fact p.Prime] {E : Subgroup (MulAut K)} (hE : CFSG.Open.IsElemAbelian p E) (hE1 : E ≠ ⊥)
    (𝓗 : Set (Subgroup (K ⧸ Subgroup.center K))) (hp' : ∀ H ∈ 𝓗, ¬ p ∣ Nat.card H)
    (hstab : ∀ H ∈ 𝓗, ∀ f ∈ E, ∀ s ∈ H, quotAut f s ∈ H) (hgen : ⨆ H ∈ 𝓗, H = ⊤) :
    seitzHyperGamma p E = ⊤ := by
  refine seitzHyperGamma_eq_top_of_quot hperf (isPGroup_of_isElemAbelian hE) ?_
  rw [← hgen]
  refine iSup₂_le fun H hH => ?_
  refine (le_closure_of_p'Subgroup hE hE1 (hp' H hH) (hstab H hH)).trans
    (Subgroup.closure_mono ?_)
  rintro s ⟨hs, hF⟩
  exact ⟨Or.inr hs, hF⟩

@[expose] def innerImage (E : Subgroup (MulAut K)) : Subgroup (K ⧸ Subgroup.center K) :=
  (E.comap (MulAut.conj : K →* MulAut K)).map (QuotientGroup.mk' (Subgroup.center K))

theorem mk_mem_innerImage {E : Subgroup (MulAut K)} {k : K} (hk : MulAut.conj k ∈ E) :
    (k : K ⧸ Subgroup.center K) ∈ innerImage E :=
  ⟨k, hk, rfl⟩

theorem seitzHyperGamma_eq_top_of_inner [Finite K] (hperf : commutator K = ⊤) {p : ℕ}
    [Fact p.Prime] {E : Subgroup (MulAut K)} (hE : CFSG.Open.IsElemAbelian p E) (hE1 : E ≠ ⊥)
    (hinn : E ≤ (MulAut.conj : K →* MulAut K).range)
    (𝓗 : Set (Subgroup (K ⧸ Subgroup.center K))) (hp' : ∀ H ∈ 𝓗, ¬ p ∣ Nat.card H)
    (hnorm : ∀ H ∈ 𝓗, ∀ e ∈ innerImage E, ∀ s ∈ H, e * s * e⁻¹ ∈ H)
    (hgen : ⨆ H ∈ 𝓗, H = ⊤) : seitzHyperGamma p E = ⊤ := by
  refine seitzHyperGamma_eq_top_of_p'Subgroups hperf hE hE1 𝓗 hp' (fun H hH f hf s hs => ?_) hgen
  obtain ⟨k, rfl⟩ := hinn hf
  rw [quotAut_conj]
  exact hnorm H hH _ (mk_mem_innerImage hf) s hs

end CFSG.LieType.SeitzGeneration.QuasiHigh
