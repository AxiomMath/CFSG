module

public import CFSG.Assembly.Subnormal

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen.AltTen

open CFSG.Open Subgroup

variable {G : Type*} [Group G]

private theorem eq_bot_of_perfect_of_isSolvable {X : Type*} [Group X] [Group.IsSolvable X]
    {D : Subgroup X} (hp : ⁅D, D⁆ = D) : D = ⊥ := by
  obtain ⟨n, hn⟩ := (Group.isSolvable_def X).mp inferInstance
  have h : ∀ k, D ≤ derivedSeries X k := by
    intro k
    induction k with
    | zero => exact le_top
    | succ k ih => rw [derivedSeries_succ, ← hp]; exact Subgroup.commutator_mono ih ih
  exact le_bot_iff.mp (hn ▸ h n)

theorem le_of_perfect_of_normal_of_le_sup [Finite G] {p : ℕ} [Fact p.Prime] {P₁ P₂ H T : Subgroup G}
    (h1 : P₁ ≤ H) (hP₁ : ⁅P₁, P₁⁆ = P₁) (h2 : P₂ ≤ H) (hn : (P₂.subgroupOf H).Normal)
    (hT : IsPGroup p T) (hHT : H ≤ normalizer (T : Set G)) (hH : H ≤ P₂ ⊔ T) : P₁ ≤ P₂ := by
  haveI := hn
  set q := QuotientGroup.mk' (P₂.subgroupOf H) with hq
  have hpq : IsPGroup p (↥H ⧸ P₂.subgroupOf H) := by
    intro y
    obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective (P₂.subgroupOf H) y
    have hmem : (h : G) ∈ ((P₂ ⊔ T : Subgroup G) : Set G) := hH h.2
    rw [Subgroup.coe_mul_of_left_le_normalizer_right P₂ T (h2.trans hHT)] at hmem
    obtain ⟨a, ha, b, hb, hab⟩ := hmem
    have hbH : b ∈ H := by
      have hb' : b = a⁻¹ * h := by rw [← hab]; group
      rw [hb']
      exact H.mul_mem (H.inv_mem (h2 ha)) h.2
    obtain ⟨k, hk⟩ := hT ⟨b, hb⟩
    refine ⟨k, ?_⟩
    have heq : q h = q ⟨b, hbH⟩ := by
      rw [hq, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
        Subgroup.mem_subgroupOf]
      have h3 : ((h⁻¹ * ⟨b, hbH⟩ : ↥H) : G) = b⁻¹ * a⁻¹ * b := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        rw [← hab]
        group
      rw [h3]
      have h4 := hn.conj_mem ⟨a⁻¹, H.inv_mem (h2 ha)⟩
        (by rw [Subgroup.mem_subgroupOf]; exact P₂.inv_mem ha) (⟨b, hbH⟩ : ↥H)⁻¹
      rw [Subgroup.mem_subgroupOf] at h4
      simpa using h4
    rw [heq, ← map_pow]
    have h5 : (⟨b, hbH⟩ : ↥H) ^ p ^ k = 1 := by
      apply Subtype.ext
      have := congrArg Subtype.val hk
      simpa using this
    rw [h5, map_one]
  haveI : Group.IsSolvable (↥H ⧸ P₂.subgroupOf H) := by
    haveI := hpq.isNilpotent
    infer_instance
  have hP₁' : ⁅P₁.subgroupOf H, P₁.subgroupOf H⁆ = P₁.subgroupOf H := by
    apply Subgroup.map_injective H.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le h1, hP₁]
  have hbot : (P₁.subgroupOf H).map q = ⊥ :=
    eq_bot_of_perfect_of_isSolvable (by rw [← Subgroup.map_commutator, hP₁'])
  intro x hx
  have hx' : q ⟨x, h1 hx⟩ ∈ (P₁.subgroupOf H).map q :=
    ⟨⟨x, h1 hx⟩, (Subgroup.mem_subgroupOf.mpr hx : (⟨x, h1 hx⟩ : ↥H) ∈ P₁.subgroupOf H), rfl⟩
  rw [hbot, Subgroup.mem_bot, hq, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
    Subgroup.mem_subgroupOf] at hx'
  exact hx'

theorem subgroupOf_normal_of_isSubnormal [Finite G] {p : ℕ} [Fact p.Prime] {T : Subgroup G}
    (hT : IsPGroup p T) {H K : Subgroup G} (hHK : IsSubnormal H K) :
    ∀ P : Subgroup G, ⁅P, P⁆ = P → P ≤ H → (P.subgroupOf H).Normal →
      K ≤ normalizer (T : Set G) → K ≤ P ⊔ T → (P.subgroupOf K).Normal := by
  induction hHK with
  | refl H => exact fun P _ _ hn _ _ => hn
  | @step H M K hHM hHMn hMK ih =>
    intro P hP hPH hPn hKT hKP
    have hMK' := hMK.le
    refine ih P hP (hPH.trans hHM) ⟨fun x hx m => ?_⟩ hKT hKP
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    have hP'H : P.map (MulAut.conj (m : G)).toMonoidHom ≤ H := by
      rintro _ ⟨y, hy, rfl⟩
      have h1 := hHMn.conj_mem ⟨y, hHM (hPH hy)⟩
        (by rw [Subgroup.mem_subgroupOf]; exact hPH hy) m
      rw [Subgroup.mem_subgroupOf] at h1
      simpa using h1
    have hP'p : ⁅P.map (MulAut.conj (m : G)).toMonoidHom,
        P.map (MulAut.conj (m : G)).toMonoidHom⁆ = P.map (MulAut.conj (m : G)).toMonoidHom := by
      rw [← Subgroup.map_commutator, hP]
    have hle := le_of_perfect_of_normal_of_le_sup hP'H hP'p hPH hPn hT ((hHM.trans hMK').trans hKT)
      ((hHM.trans hMK').trans hKP)
    have h2 := hle ⟨(x : G), hx, rfl⟩
    simpa using h2

theorem eq_of_perfect_of_isSubnormal [Finite G] {p : ℕ} [Fact p.Prime] {T K₁ K₂ R : Subgroup G}
    (hT : IsPGroup p T) (hRT : R ≤ normalizer (T : Set G))
    (h₁ : IsSubnormal K₁ R) (h₂ : IsSubnormal K₂ R) (hp₁ : ⁅K₁, K₁⁆ = K₁) (hp₂ : ⁅K₂, K₂⁆ = K₂)
    (hR₁ : R ≤ K₁ ⊔ T) (hR₂ : R ≤ K₂ ⊔ T) : K₁ = K₂ := by
  have hn₁ := subgroupOf_normal_of_isSubnormal hT h₁ K₁ hp₁ le_rfl
    (by rw [Subgroup.subgroupOf_self]; infer_instance) hRT hR₁
  have hn₂ := subgroupOf_normal_of_isSubnormal hT h₂ K₂ hp₂ le_rfl
    (by rw [Subgroup.subgroupOf_self]; infer_instance) hRT hR₂
  exact le_antisymm (le_of_perfect_of_normal_of_le_sup h₁.le hp₁ h₂.le hn₂ hT hRT hR₂)
    (le_of_perfect_of_normal_of_le_sup h₂.le hp₂ h₁.le hn₁ hT hRT hR₁)

theorem eq_alternatingGroup_of_perfect {n : ℕ} {D : Subgroup (Equiv.Perm (Fin n))} (hD : D ≠ ⊥)
    (hp : ⁅D, D⁆ = D) (hs : D.IsSubnormal) : 5 ≤ n ∧ D = alternatingGroup (Fin n) := by
  by_cases hn : n ≤ 4
  · have : Group.IsSolvable (Equiv.Perm (Fin n)) := Equiv.Perm.isSolvable (by simpa using hn)
    exact absurd (eq_bot_of_perfect_of_isSolvable hp) hD
  push Not at hn
  have hDA : D ≤ alternatingGroup (Fin n) := by
    rw [← hp, Subgroup.commutator_le]
    intro a _ b _
    rw [Equiv.Perm.mem_alternatingGroup, commutatorElement_def, map_mul, map_mul, map_mul,
      map_inv, map_inv, mul_comm (Equiv.Perm.sign a) (Equiv.Perm.sign b)]
    group
  have hsimp : IsSimpleGroup (alternatingGroup (Fin n)) :=
    alternatingGroup.isSimpleGroup (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; omega)
  have hs' : (D.subgroupOf (alternatingGroup (Fin n))).IsSubnormal := hs.subgroupOf
  refine ⟨by omega, ?_⟩
  rcases hs'.eq_bot_or_top_of_isSimpleGroup hsimp with h | h
  · exfalso
    apply hD
    rw [← Subgroup.map_subgroupOf_eq_of_le hDA, h, Subgroup.map_bot]
  · refine le_antisymm hDA fun a ha => ?_
    have : (⟨a, ha⟩ : ↥(alternatingGroup (Fin n))) ∈ D.subgroupOf (alternatingGroup (Fin n)) := by
      rw [h]; exact Subgroup.mem_top _
    exact this

theorem exists_surjective_alt5_of_ker {I C : Type*} [Group I] [Group C] [Finite I]
    (f : I →* alternatingGroup (Fin 5)) (hf : Function.Surjective f) (π : I →* C)
    (hπ : Function.Surjective π) (hk : IsPGroup 2 π.ker) :
    ∃ g : C →* alternatingGroup (Fin 5), Function.Surjective g := by
  haveI hsimp : IsSimpleGroup (alternatingGroup (Fin 5)) :=
    alternatingGroup.isSimpleGroup (by norm_num [Nat.card_eq_fintype_card])
  have hle : π.ker ≤ f.ker := by
    haveI hN : (π.ker.map f).Normal := (MonoidHom.normal_ker π).map f hf
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (π.ker.map f) with h | h
    · intro x hx
      have : f x ∈ π.ker.map f := ⟨x, hx, rfl⟩
      rw [h, Subgroup.mem_bot] at this
      exact this
    · exfalso
      have h2 : IsPGroup 2 (⊤ : Subgroup (alternatingGroup (Fin 5))) := h ▸ hk.map f
      haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      obtain ⟨k, hk'⟩ := h2.exists_card_eq
      rw [Subgroup.card_top, nat_card_alternatingGroup, Nat.card_fin] at hk'
      have h3 : (3 : ℕ) ∣ 2 ^ k := by rw [← hk']; decide
      have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
        (Nat.prime_three.dvd_of_dvd_pow h3)
      omega
  refine ⟨(MonoidHom.liftOfSurjective π hπ) ⟨f, hle⟩, fun a => ?_⟩
  obtain ⟨y, rfl⟩ := hf a
  exact ⟨π y, MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ _⟩

theorem card_eq_sixty_of_isSimpleGroup {Q : Type*} [Group Q] [IsSimpleGroup Q]
    (g : Q →* alternatingGroup (Fin 5)) (hg : Function.Surjective g) : Nat.card Q = 60 := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal g.ker with h | h
  · have hinj : Function.Injective g := (MonoidHom.ker_eq_bot_iff g).mp h
    rw [Nat.card_congr (Equiv.ofBijective g ⟨hinj, hg⟩), nat_card_alternatingGroup, Nat.card_fin]
    rfl
  · exfalso
    haveI : IsSimpleGroup (alternatingGroup (Fin 5)) :=
      alternatingGroup.isSimpleGroup (by norm_num [Nat.card_eq_fintype_card])
    obtain ⟨a, ha⟩ := exists_ne (1 : alternatingGroup (Fin 5))
    obtain ⟨y, rfl⟩ := hg a
    exact ha ((MonoidHom.mem_ker).mp (h ▸ Subgroup.mem_top y))

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen.AltTen
