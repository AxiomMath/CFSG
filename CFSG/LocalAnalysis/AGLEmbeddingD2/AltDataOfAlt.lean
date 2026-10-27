module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.AltData
public import CFSG.LocalAnalysis.AGLEmbeddingD2.AltDataPerm
public import CFSG.LocalAnalysis.AGLEmbeddingD2.SurvivorBridge

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.Open CFSG.PreuniquenessRankFour.Helpers CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.AGLEmbedding

variable {G : Type} [Group G] [Finite G]

section Model

open AltSurvivor Equiv

variable {X : Type} [Group X] [Finite X] {p : ℕ} {R : Sylow p X} {A X₀ K : Subgroup X}

structure D2AltModel (p : ℕ) {X : Type} [Group X] (A X₀ K : Subgroup X)
    (e : K ≃* alternatingGroup (Fin (2 * p))) where
  ι : X →* Perm (Fin (2 * p))
  a₁ : X
  a₂ : X
  O₁ : Finset (Fin (2 * p))
  O₂ : Finset (Fin (2 * p))
  injective : Function.Injective ι
  ι_val : ∀ k : K, ι (k : X) = ((e k : alternatingGroup (Fin (2 * p))) : Perm (Fin (2 * p)))
  mem₁ : a₁ ∈ A
  mem₂ : a₂ ∈ A
  card₁ : O₁.card = p
  card₂ : O₂.card = p
  disjoint : Disjoint O₁ O₂
  cover : ∀ x, x ∈ O₁ ∨ x ∈ O₂
  supp₁ : ∀ x, ι a₁ x ≠ x ↔ x ∈ O₁
  supp₂ : ∀ x, ι a₂ x ≠ x ↔ x ∈ O₂
  cycle₁ : (ι a₁).IsCycle
  cycle₂ : (ι a₂).IsCycle
  altOn₁ : altOn O₁ ≤ X₀.map ι
  altOn₂ : altOn O₂ ≤ X₀.map ι
  preserves : ∀ y ∈ X₀.map ι, (∀ x, x ∈ O₁ ↔ y x ∈ O₁) ∨ (∀ x, x ∈ O₁ ↔ y x ∈ O₂)

theorem D2AlmostSimple.nonempty_altModel (h : D2AlmostSimple p X R A X₀ K) (hp5 : 5 ≤ p)
    (e : K ≃* alternatingGroup (Fin (2 * p))) : Nonempty (D2AltModel p A X₀ K e) := by
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  have : K.Normal := h.normal
  obtain ⟨ι, a₁, a₂, O₁, O₂, hι, hιK, ha₁, ha₂, hO₁, hO₂, hd, hcov, hs₁, hs₂, hcy₁, hcy₂⟩ :=
    h.exists_cycle_data hp5 e
  have ha₁1 : a₁ ≠ 1 := fun h1 => hcy₁.ne_one (by rw [h1, map_one])
  have ha₂1 : a₂ ≠ 1 := fun h1 => hcy₂.ne_one (by rw [h1, map_one])
  set Y : Subgroup (Perm (Fin (2 * p))) := X₀.map ι with hYdef
  have hN : ∀ a ∈ A, a ≠ 1 → Subgroup.centralizer ({a} : Set X) ≤ X₀ := fun a haA ha1 g hg =>
    h.normalizer_le_of_le_A (Subgroup.zpowers a) (Subgroup.zpowers_le.mpr haA)
      (by rwa [Ne, Subgroup.zpowers_eq_bot]) (centralizer_singleton_le_normalizer_zpowers _ hg)
  have hAlt : ∀ a ∈ A, a ≠ 1 → ∀ O O' : Finset (Fin (2 * p)), (∀ x, ι a x ≠ x ↔ x ∈ O') →
      Disjoint O O' → altOn O ≤ Y := by
    intro a haA ha1 O O' hsO' hdis g hg
    rw [mem_altOn] at hg
    let g' : alternatingGroup (Fin (2 * p)) := ⟨g, Perm.mem_alternatingGroup.mpr hg.1⟩
    let k : K := e.symm g'
    have hk : ι (k : X) = g := by
      rw [hιK]
      simp [k, g']
    have hcomm : (k : X) * a = a * (k : X) := by
      apply hι
      rw [map_mul, map_mul, hk]
      refine (Perm.Disjoint.commute fun x => ?_).eq
      by_cases hx : x ∈ O
      · right
        by_contra hne
        exact Finset.disjoint_left.mp hdis hx ((hsO' x).mp hne)
      · left
        exact hg.2 x hx
    exact ⟨k, hN a haA ha1 (Subgroup.mem_centralizer_singleton_iff.mpr hcomm), hk⟩
  have hY₁ : altOn O₁ ≤ Y := hAlt a₂ ha₂ ha₂1 O₁ O₂ hs₂ hd
  have hY₂ : altOn O₂ ≤ Y := hAlt a₁ ha₁ ha₁1 O₂ O₁ hs₁ hd.symm
  have hor : ∀ y ∈ Y, (∀ x ∈ O₁, y x ∈ O₁) ∨ (∀ x ∈ O₁, y x ∈ O₂) := by
    intro y hy
    by_contra hcon
    push Not at hcon
    obtain ⟨⟨u, hu, huy⟩, ⟨w, hw, hwy⟩⟩ := hcon
    have hu' : y u ∈ O₂ := (hcov _).resolve_left huy
    have hw' : y w ∈ O₁ := (hcov _).resolve_right hwy
    have hAltY := alternatingGroup_le_of_cross hd hcov (by omega) (by omega) hY₁ hY₂ hy hu hu'
      hw hw'
    apply h.not_le
    intro k hk
    have hmem : ι k ∈ Y := hAltY (by
      rw [show ι k = ι ((⟨k, hk⟩ : K) : X) from rfl, hιK ⟨k, hk⟩]
      exact (e ⟨k, hk⟩).2)
    obtain ⟨x, hx, hxk⟩ := Subgroup.mem_map.mp hmem
    exact (hι hxk) ▸ hx
  exact ⟨{
    ι := ι
    a₁ := a₁
    a₂ := a₂
    O₁ := O₁
    O₂ := O₂
    injective := hι
    ι_val := hιK
    mem₁ := ha₁
    mem₂ := ha₂
    card₁ := hO₁
    card₂ := hO₂
    disjoint := hd
    cover := hcov
    supp₁ := hs₁
    supp₂ := hs₂
    cycle₁ := hcy₁
    cycle₂ := hcy₂
    altOn₁ := hY₁
    altOn₂ := hY₂
    preserves := fun y hy => iff_of_forall_mem_or (hO₁.trans hO₂.symm) (hor y hy) }⟩

end Model

section Reduced

open AltSurvivor Equiv

variable {X : Type} [Group X] {p : ℕ} {A X₀ K : Subgroup X}
  {e : K ≃* alternatingGroup (Fin (2 * p))}

namespace D2AltModel

theorem exists_zpow_eq (M : D2AltModel p A X₀ K e) (hAc : ∀ u v : A, u * v = v * u) {x : X}
    (hx : x ∈ A) : ∃ i j : ℤ, x = M.a₁ ^ i * M.a₂ ^ j := by
  have hc : ∀ a ∈ A, x * a = a * x := fun a ha => congrArg Subtype.val (hAc ⟨x, hx⟩ ⟨a, ha⟩)
  have h₁ : M.ι x * M.ι M.a₁ = M.ι M.a₁ * M.ι x := by
    rw [← map_mul, ← map_mul, hc _ M.mem₁]
  have h₂ : M.ι x * M.ι M.a₂ = M.ι M.a₂ * M.ι x := by
    rw [← map_mul, ← map_mul, hc _ M.mem₂]
  obtain ⟨i, j, hij⟩ := exists_zpow_mul_zpow_eq M.cycle₁ M.cycle₂ M.supp₁ M.supp₂ M.disjoint
    M.cover h₁ h₂
  exact ⟨i, j, M.injective (by rw [hij, map_mul, map_zpow, map_zpow])⟩

theorem mem₂_iff (M : D2AltModel p A X₀ K e) (x : Fin (2 * p)) : x ∈ M.O₂ ↔ x ∉ M.O₁ :=
  ⟨fun h h' => Finset.disjoint_left.mp M.disjoint h' h, fun h => (M.cover x).resolve_left h⟩

theorem preserves₂ (M : D2AltModel p A X₀ K e) {y : Perm (Fin (2 * p))} (hy : y ∈ X₀.map M.ι) :
    (∀ x, x ∈ M.O₂ ↔ y x ∈ M.O₂) ∨ (∀ x, x ∈ M.O₂ ↔ y x ∈ M.O₁) := by
  rcases M.preserves y hy with h | h
  · refine Or.inl fun x => ?_
    have := h x
    have := M.mem₂_iff x
    have := M.mem₂_iff (y x)
    tauto
  · refine Or.inr fun x => ?_
    have := h x
    have := M.mem₂_iff x
    have := M.mem₂_iff (y x)
    tauto

theorem ι_a₁_mem (M : D2AltModel p A X₀ K e) (hodd : Odd p) (hpow : M.a₁ ^ p = 1) :
    M.ι M.a₁ ∈ altOn M.O₁ := by
  rw [mem_altOn]
  refine ⟨AltThree.sign_eq_one_of_pow_eq_one hodd ?_, fun x hx => ?_⟩
  · rw [← map_pow, hpow, map_one]
  · by_contra hne
    exact hx ((M.supp₁ x).mp hne)

theorem ι_a₂_mem (M : D2AltModel p A X₀ K e) (hodd : Odd p) (hpow : M.a₂ ^ p = 1) :
    M.ι M.a₂ ∈ altOn M.O₂ := by
  rw [mem_altOn]
  refine ⟨AltThree.sign_eq_one_of_pow_eq_one hodd ?_, fun x hx => ?_⟩
  · rw [← map_pow, hpow, map_one]
  · by_contra hne
    exact hx ((M.supp₂ x).mp hne)

theorem conj_mem_sup (M : D2AltModel p A X₀ K e) {y : X} (hy : y ∈ X₀) {g : Perm (Fin (2 * p))}
    (hg : g ∈ altOn M.O₁ ⊔ altOn M.O₂) :
    M.ι y * g * (M.ι y)⁻¹ ∈ altOn M.O₁ ⊔ altOn M.O₂ := by
  have hyY : M.ι y ∈ X₀.map M.ι := Subgroup.mem_map_of_mem M.ι hy
  have h₁ := M.preserves _ hyY
  have h₂ := M.preserves₂ hyY
  have hmap : (altOn M.O₁ ⊔ altOn M.O₂).map (MulAut.conj (M.ι y)).toMonoidHom ≤
      altOn M.O₁ ⊔ altOn M.O₂ := by
    rw [Subgroup.map_sup]
    refine sup_le ?_ ?_
    · rintro _ ⟨g, hg, rfl⟩
      rcases h₁ with h | h
      · exact Subgroup.mem_sup_left (conj_mem_altOn h hg)
      · exact Subgroup.mem_sup_right (conj_mem_altOn h hg)
    · rintro _ ⟨g, hg, rfl⟩
      rcases h₂ with h | h
      · exact Subgroup.mem_sup_right (conj_mem_altOn h hg)
      · exact Subgroup.mem_sup_left (conj_mem_altOn h hg)
  exact hmap ⟨g, hg, rfl⟩

end D2AltModel

end Reduced

section ReducedFinite

open AltSurvivor Equiv

variable {X : Type} [Group X] {p : ℕ} {A X₀ K : Subgroup X}
  {e : K ≃* alternatingGroup (Fin (2 * p))}

namespace D2AltModel

@[expose] def B (M : D2AltModel p A X₀ K e) : Subgroup X := (altOn M.O₁ ⊔ altOn M.O₂).comap M.ι

theorem mem_B_iff (M : D2AltModel p A X₀ K e) {x : X} :
    x ∈ M.B ↔ M.ι x ∈ altOn M.O₁ ⊔ altOn M.O₂ := Iff.rfl

theorem sup_le_range (M : D2AltModel p A X₀ K e) : altOn M.O₁ ⊔ altOn M.O₂ ≤ M.ι.range :=
  (sup_le M.altOn₁ M.altOn₂).trans (Subgroup.map_le_range _ _)

theorem map_B (M : D2AltModel p A X₀ K e) : M.B.map M.ι = altOn M.O₁ ⊔ altOn M.O₂ :=
  Subgroup.map_comap_eq_self M.sup_le_range

theorem B_le (M : D2AltModel p A X₀ K e) : M.B ≤ X₀ := by
  intro x hx
  obtain ⟨y, hy, hyx⟩ := (sup_le M.altOn₁ M.altOn₂) hx
  exact (M.injective hyx) ▸ hy

theorem B_perfect (M : D2AltModel p A X₀ K e) (hp5 : 5 ≤ p) : ⁅M.B, M.B⁆ = M.B := by
  apply Subgroup.map_injective M.injective
  rw [Subgroup.map_commutator, M.map_B,
    AltData.commutator_altOn_sup (by rw [M.card₁]; exact hp5) (by rw [M.card₂]; exact hp5)]

theorem mem_normalizer_B [Finite X] (M : D2AltModel p A X₀ K e) {y : X} (hy : y ∈ X₀) :
    y ∈ Subgroup.normalizer (M.B : Set X) :=
  AltData.mem_normalizer_of_conj_mem fun x hx => M.mem_B_iff.mpr (by
    rw [map_mul, map_mul, map_inv]
    exact M.conj_mem_sup hy hx)

theorem A_le_B (M : D2AltModel p A X₀ K e) (hodd : Odd p) (hAc : ∀ u v : A, u * v = v * u)
    (hexp : ∀ a ∈ A, a ^ p = 1) : A ≤ M.B := by
  intro x hx
  obtain ⟨i, j, rfl⟩ := M.exists_zpow_eq hAc hx
  rw [mem_B_iff, map_mul, map_zpow, map_zpow]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.zpow_mem _
    (M.ι_a₁_mem hodd (hexp _ M.mem₁)) i))
    (Subgroup.mem_sup_right (Subgroup.zpow_mem _ (M.ι_a₂_mem hodd (hexp _ M.mem₂)) j))

end D2AltModel

end ReducedFinite

section ReducedAlmostSimple

open AltSurvivor Equiv

variable {X : Type} [Group X] [Finite X] {p : ℕ} {R : Sylow p X} {A X₀ K : Subgroup X}
  {e : K ≃* alternatingGroup (Fin (2 * p))}

theorem D2AlmostSimple.exists_swap_elem (h : D2AlmostSimple p X R A X₀ K)
    (M : D2AltModel p A X₀ K e) {g : ℕ} (hg : orderOf (g : ZMod p) = p - 1) :
    ∃ k : X, k ∈ Subgroup.normalizer (A : Set X) ∧ k * M.a₁ * k⁻¹ = M.a₂ ∧
      k * M.a₂ * k⁻¹ = M.a₁ ^ g ∧ ∀ x, x ∈ M.O₁ ↔ M.ι k x ∈ M.O₂ := by
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  have hp₁ : (M.ι M.a₁) ^ p = 1 := by rw [← map_pow, h.elem.2 M.a₁ M.mem₁, map_one]
  have hp₂ : (M.ι M.a₂) ^ p = 1 := by rw [← map_pow, h.elem.2 M.a₂ M.mem₂, map_one]
  obtain ⟨σ, hsign, hσ₁, hσ₂, hσO⟩ := AltData.exists_swap_perm h.ne_two hg M.cycle₁ M.cycle₂ hp₁
    hp₂ M.supp₁ M.supp₂ M.card₁ M.card₂ M.disjoint
  let k : K := e.symm ⟨σ, Perm.mem_alternatingGroup.mpr hsign⟩
  have hk : M.ι (k : X) = σ := by
    rw [M.ι_val]
    simp [k]
  have hk₁ : (k : X) * M.a₁ * (k : X)⁻¹ = M.a₂ := by
    apply M.injective
    rw [map_mul, map_mul, map_inv, hk, mul_inv_eq_iff_eq_mul]
    exact hσ₁
  have hk₂ : (k : X) * M.a₂ * (k : X)⁻¹ = M.a₁ ^ g := by
    apply M.injective
    rw [map_mul, map_mul, map_inv, hk, map_pow, mul_inv_eq_iff_eq_mul]
    exact hσ₂
  have hAc : ∀ u v : A, u * v = v * u := isMulCommutative_iff.1 h.elem.1
  refine ⟨k, AltData.mem_normalizer_of_conj_mem fun x hx => ?_, hk₁, hk₂, ?_⟩
  · obtain ⟨i, j, rfl⟩ := M.exists_zpow_eq hAc hx
    have : (k : X) * (M.a₁ ^ i * M.a₂ ^ j) * (k : X)⁻¹ =
        ((k : X) * M.a₁ * (k : X)⁻¹) ^ i * ((k : X) * M.a₂ * (k : X)⁻¹) ^ j := by
      rw [conj_zpow, conj_zpow]
      group
    rw [this, hk₁, hk₂]
    exact A.mul_mem (A.zpow_mem M.mem₂ i) (A.zpow_mem (A.pow_mem M.mem₁ g) j)
  · rw [hk]
    exact hσO

end ReducedAlmostSimple

section ReducedAlmostSimple2

open AltSurvivor Equiv

variable {X : Type} [Group X] [Finite X] {p : ℕ} {R : Sylow p X} {A X₀ K : Subgroup X}
  {e : K ≃* alternatingGroup (Fin (2 * p))}

theorem D2AlmostSimple.eq_bot_of_isPGroup (h : D2AlmostSimple p X R A X₀ K) (hp5 : 5 ≤ p)
    (M : D2AltModel p A X₀ K e) {W : Subgroup X} (hWX : W ≤ X₀)
    (hWn : X₀ ≤ Subgroup.normalizer (W : Set X)) (hWp : IsPGroup p W) : W = ⊥ := by
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  have hodd : Odd p := hp.eq_two_or_odd'.resolve_left h.ne_two
  rcases h.dichotomy_of_alternating hp5 e hWX hWn with hbot | hA
  · exact hbot
  exfalso
  have ha₂W : M.a₂ ∈ W := hA M.mem₂
  have hVn : ∀ l ∈ altOn M.O₂, ∀ v ∈ W.map M.ι, l * v * l⁻¹ ∈ W.map M.ι := by
    rintro l hl _ ⟨w, hw, rfl⟩
    obtain ⟨y, hy, rfl⟩ := M.altOn₂ hl
    exact ⟨y * w * y⁻¹, (Subgroup.mem_normalizer_iff.mp (hWn hy) w).mp hw, by simp⟩
  have hb₂ : M.ι M.a₂ ∈ altOn M.O₂ := M.ι_a₂_mem hodd (h.elem.2 M.a₂ M.mem₂)
  rcases inf_altOn_eq_bot_or_le (by rw [M.card₂]; exact hp5) hVn with hbot | hle
  · have : M.ι M.a₂ ∈ W.map M.ι ⊓ altOn M.O₂ := ⟨Subgroup.mem_map_of_mem M.ι ha₂W, hb₂⟩
    rw [hbot, Subgroup.mem_bot] at this
    exact M.cycle₂.ne_one this
  ·
    obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ := Finset.two_lt_card_iff.mp
      (by rw [M.card₂]; omega : 2 < M.O₂.card)
    have h3 : swap a b * swap b c ∈ altOn M.O₂ := swap_mul_swap_mem_altOn ha hb hc hab hbc
    obtain ⟨w, hw, hwc⟩ := hle h3
    obtain ⟨k, hk⟩ := hWp ⟨w, hw⟩
    have hwk : w ^ p ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hord : orderOf (swap a b * swap b c) = 3 :=
      (AltGen.isThreeCycle_swap_mul_swap hab hac hbc).orderOf
    have hdvd : 3 ∣ p ^ k := by
      rw [← hord]
      refine orderOf_dvd_of_pow_eq_one ?_
      rw [← hwc, ← map_pow, hwk, map_one]
    have h3p : 3 ∣ p := Nat.Prime.dvd_of_dvd_pow Nat.prime_three hdvd
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp h3p
    omega

end ReducedAlmostSimple2

section Lift

variable {p : ℕ} [Fact p.Prime] {H A : Subgroup G}

theorem AltData.eq_of_mk_eq (hA : IsPGroup p A) {x y : H} (hx : (x : G) ∈ A) (hy : (y : G) ∈ A)
    (hxy : QuotientGroup.mk' (primeComplementCore (G := H) p) x =
      QuotientGroup.mk' (primeComplementCore (G := H) p) y) : x = y := by
  have hker : x⁻¹ * y ∈ primeComplementCore (G := H) p := by
    rw [← QuotientGroup.ker_mk' (primeComplementCore (G := H) p), MonoidHom.mem_ker, map_mul,
      map_inv, hxy, inv_mul_cancel]
  have hA' : IsPGroup p (A.subgroupOf H) := hA.comap_subtype
  have hmem : x⁻¹ * y ∈ A.subgroupOf H ⊓ primeComplementCore (G := H) p :=
    ⟨Subgroup.mem_subgroupOf.mpr (by simpa using A.mul_mem (A.inv_mem hx) hy), hker⟩
  rw [inf_eq_bot_of_isPGroup Fact.out hA' (primeComplementCore_coprime p),
    Subgroup.mem_bot] at hmem
  exact inv_mul_eq_one.mp hmem

theorem AltData.exists_normalizer_lift (hAH : A ≤ H) (hA : IsPGroup p A)
    {k : H ⧸ primeComplementCore (G := H) p}
    (hk : k ∈ Subgroup.normalizer (((A.subgroupOf H).map
      (QuotientGroup.mk' (primeComplementCore (G := H) p)) : Subgroup _) : Set _)) :
    ∃ t : H, (t : G) ∈ Subgroup.normalizer (A : Set G) ∧
      QuotientGroup.mk' (primeComplementCore (G := H) p) t = k := by
  obtain ⟨h₀, rfl⟩ := QuotientGroup.mk'_surjective (primeComplementCore (G := H) p) k
  have hmem : h₀ ∈ primeComplementCore (G := H) p ⊔
      Subgroup.normalizer ((A.subgroupOf H : Subgroup H) : Set H) :=
    comap_normalizer_map_le_sup Fact.out (primeComplementCore (G := H) p)
      (primeComplementCore_coprime p) hA.comap_subtype hk
  obtain ⟨o, ho, t, ht, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hmem
  refine ⟨t, ?_, ?_⟩
  · have := Subgroup.le_normalizer_map H.subtype ⟨t, ht, rfl⟩
    rwa [Subgroup.map_subgroupOf_eq_of_le hAH] at this
  · have ho1 : QuotientGroup.mk' (primeComplementCore (G := H) p) o = 1 :=
      (QuotientGroup.eq_one_iff o).mpr ho
    rw [map_mul, ho1, one_mul]

omit [Fact p.Prime] in
theorem AltData.exists_nat_orderOf_eq (p : ℕ) [Fact p.Prime] :
    ∃ g : ℕ, orderOf (g : ZMod p) = p - 1 := by
  obtain ⟨u, hu⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
  refine ⟨(u : ZMod p).val, ?_⟩
  rw [ZMod.natCast_zmod_val, orderOf_units, orderOf_eq_card_of_forall_mem_zpowers hu,
    Nat.card_eq_fintype_card, ZMod.card_units]

end Lift

variable {p : ℕ} {P : Sylow p G} {M A H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}

open AltSurvivor in
theorem D2Escape.perfect_of_alt [Fact p.Prime] (h : D2Escape p P M A H R)
    (hK : D2AlmostSimple p _ Rbar ((A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)))
      (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p))) K)
    (e : K ≃* alternatingGroup (Fin (2 * p))) (hp5 : 5 ≤ p) :
    ∃ (c₀ c₁ s : G) (g : ℕ) (W : Subgroup G)
      (ψ : W →* alternatingGroup (Fin p) × alternatingGroup (Fin p)),
      AltScalar p (H ⊓ M) A c₀ c₁ s g ∧ W ≤ H ⊓ M ∧ ⁅W, W⁆ = W ∧ A ≤ W ∧
      H ⊓ M ≤ Subgroup.normalizer (W : Set G) ∧ Function.Surjective ψ ∧
      ψ.ker = (GLBPrimeCore p H).subgroupOf W ∧
      (∀ w : W, (w : G) = c₀ → (ψ w).2 = 1) ∧ (∀ w : W, (w : G) = c₁ → (ψ w).1 = 1) ∧
      ∀ w w' : W, (w' : G) = s * w * s⁻¹ →
        ((ψ w).2 = 1 → (ψ w').1 = 1) ∧ ((ψ w).1 = 1 → (ψ w').2 = 1) := by
  classical
  have hp : p.Prime := h.prime
  have hodd : Odd p := hp.eq_two_or_odd'.resolve_left h.ne_two
  have hAH : A ≤ H := h.A_le_H
  have hAp : IsPGroup p A := h.isPGroup.to_le h.A_le
  have hA1 : A ≠ ⊥ := by
    intro hbot
    have hc := h.card_A
    rw [hbot, Subgroup.card_bot] at hc
    have := Nat.one_lt_pow two_ne_zero hp.one_lt
    omega
  have hOM : primeComplementCore (G := H) p ≤ (H ⊓ M).subgroupOf H := by
    rw [← glbPrimeCore_subgroupOf]
    exact glbPrimeCore_subgroupOf_le_inf h.primeCore_le
  set π := QuotientGroup.mk' (primeComplementCore (G := H) p) with hπ
  obtain ⟨Mo⟩ := hK.nonempty_altModel hp5 e
  obtain ⟨g, hg⟩ := AltData.exists_nat_orderOf_eq p
  obtain ⟨k, hkN, hk₁, hk₂, hkO⟩ := hK.exists_swap_elem Mo hg
  obtain ⟨c₀', hc₀', hc₀π⟩ := Subgroup.mem_map.mp Mo.mem₁
  obtain ⟨c₁', hc₁', hc₁π⟩ := Subgroup.mem_map.mp Mo.mem₂
  obtain ⟨t, htN, htk⟩ := AltData.exists_normalizer_lift hAH hAp hkN
  have hc₀A : (c₀' : G) ∈ A := Subgroup.mem_subgroupOf.mp hc₀'
  have hc₁A : (c₁' : G) ∈ A := Subgroup.mem_subgroupOf.mp hc₁'
  have htM : (t : G) ∈ M := h.normalizer_le_of_le_A le_rfl hA1 htN
  have hAc : ∀ u v : (A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)),
      u * v = v * u := isMulCommutative_iff.1 hK.elem.1
  set c₀ : G := (c₀' : G) with hc₀
  set c₁ : G := (c₁' : G) with hc₁
  set s : G := (t : G) with hs
  have hπt : ∀ y : H, π (t * y * t⁻¹) = k * π y * k⁻¹ := fun y => by
    rw [map_mul, map_mul, map_inv, htk]
  have hconj₀ : t * c₀' * t⁻¹ = c₁' := by
    refine AltData.eq_of_mk_eq hAp ?_ hc₁A ?_
    · have := (Subgroup.mem_normalizer_iff.mp htN c₀).mp hc₀A
      simpa using this
    · rw [hπt, hc₀π, hc₁π, hk₁]
  have hconj₁ : t * c₁' * t⁻¹ = c₀' ^ g := by
    refine AltData.eq_of_mk_eq hAp ?_ ?_ ?_
    · have := (Subgroup.mem_normalizer_iff.mp htN c₁).mp hc₁A
      simpa using this
    · simpa using A.pow_mem hc₀A g
    · rw [hπt, hc₁π, map_pow, hc₀π, hk₂]
  have hspan : A = Subgroup.zpowers c₀ ⊔ Subgroup.zpowers c₁ := by
    refine le_antisymm (fun x hx => ?_)
      (sup_le (Subgroup.zpowers_le.mpr hc₀A) (Subgroup.zpowers_le.mpr hc₁A))
    have hxH : x ∈ H := hAH hx
    have hπx : π ⟨x, hxH⟩ ∈ (A.subgroupOf H).map π :=
      Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr hx)
    obtain ⟨i, j, hij⟩ := Mo.exists_zpow_eq hAc hπx
    have hxeq : (⟨x, hxH⟩ : H) = c₀' ^ i * c₁' ^ j := by
      refine AltData.eq_of_mk_eq hAp hx ?_ ?_
      · simpa using A.mul_mem (A.zpow_mem hc₀A i) (A.zpow_mem hc₁A j)
      · rw [hij, map_mul, map_zpow, map_zpow, hc₀π, hc₁π]
    have hx' : x = c₀ ^ i * c₁ ^ j := by simpa using congrArg Subtype.val hxeq
    rw [hx']
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.zpow_mem_zpowers _ i))
      (Subgroup.mem_sup_right (Subgroup.zpow_mem_zpowers _ j))
  have hscalar : AltScalar p (H ⊓ M) A c₀ c₁ s g :=
    ⟨hspan, ⟨t.2, htM⟩, htN, hg, by simpa using congrArg Subtype.val hconj₀,
      by simpa using congrArg Subtype.val hconj₁⟩
  have hBperf := Mo.B_perfect hp5
  obtain ⟨WH, hWH1, hWH2, hWH3, hWH4⟩ := AltData.exists_perfect_lift π hBperf (by
    rw [MonoidHom.range_eq_top_of_surjective _ (QuotientGroup.mk'_surjective _)]
    exact le_top)
  let Λe := AltData.altPairEquiv Mo.card₁ Mo.card₂ Mo.disjoint
  obtain ⟨ψH, hψ1, hψ2, hψ3⟩ := AltData.exists_hom_onto π Mo.ι Mo.injective Λe Mo.sup_le_range
    WH hWH3
  let W : Subgroup G := WH.map H.subtype
  let φ : WH ≃* W := Subgroup.equivMapOfInjective WH H.subtype H.subtype_injective
  let ψ : W →* alternatingGroup (Fin p) × alternatingGroup (Fin p) :=
    ψH.comp φ.symm.toMonoidHom
  have hφ : ∀ w : W, (((φ.symm w : WH) : H) : G) = (w : G) := by
    intro w
    have h1 : ((φ (φ.symm w) : W) : G) = (w : G) := by rw [φ.apply_symm_apply]
    rw [← h1]
    rfl
  have hWK : W ≤ H ⊓ M := by
    rintro _ ⟨y, hy, rfl⟩
    have hπy : π y ∈ ((H ⊓ M).subgroupOf H).map π := Mo.B_le (hWH1 hy)
    have hy' : y ∈ (((H ⊓ M).subgroupOf H).map π).comap π := hπy
    rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk', sup_eq_left.mpr hOM] at hy'
    exact Subgroup.mem_subgroupOf.mp hy'
  have hWW : ⁅W, W⁆ = W := by
    show ⁅WH.map H.subtype, WH.map H.subtype⁆ = WH.map H.subtype
    rw [← Subgroup.map_commutator, hWH2]
  have hnorm : ∀ y : H, π y ∈ Subgroup.normalizer (Mo.B : Set _) →
      (y : G) ∈ Subgroup.normalizer (W : Set G) := fun y hy =>
    Subgroup.le_normalizer_map H.subtype
      ⟨y, AltData.mem_normalizer_of_perfect_lift π hWH4 hWH1 hWH2 hy, rfl⟩
  have hKnorm : H ⊓ M ≤ Subgroup.normalizer (W : Set G) := by
    intro x hx
    exact hnorm ⟨x, hx.1⟩ (Mo.mem_normalizer_B
      (Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr hx)))
  have hAW : A ≤ W := by
    refine le_of_le_sup_of_isPGroup_of_coprime hAp (glbPrimeCore_coprime p H) ?_ ?_
    · intro n hn
      have hnH : n ∈ H := glbPrimeCore_le p H hn
      refine hnorm ⟨n, hnH⟩ ?_
      rw [(mem_glbPrimeCore_iff_mk_eq_one ⟨n, hnH⟩).mp hn]
      exact Subgroup.one_mem _
    · intro a ha
      have haH : a ∈ H := hAH ha
      have hAB := Mo.A_le_B hodd hAc (fun a ha => hK.elem.2 a ha)
      have hmem : π ⟨a, haH⟩ ∈ WH.map π := by
        rw [hWH3]
        exact hAB (Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr ha))
      obtain ⟨w, hw, hwa⟩ := hmem
      have hkn : ((w⁻¹ * ⟨a, haH⟩ : H) : G) ∈ GLBPrimeCore p H :=
        (mem_glbPrimeCore_iff_mk_eq_one _).mpr (by rw [map_mul, map_inv, hwa, inv_mul_cancel])
      have hae : a = (w : G) * ((w⁻¹ * ⟨a, haH⟩ : H) : G) := by simp
      rw [hae]
      exact Subgroup.mul_mem_sup (⟨w, hw, rfl⟩ : (w : G) ∈ W) hkn
  have hψsurj : Function.Surjective ψ := hψ1.comp φ.symm.surjective
  have hψdef : ∀ w : W, (Λe (ψ w) : Equiv.Perm (Fin (2 * p))) = Mo.ι (π ((φ.symm w : WH) : H)) :=
    fun w => hψ3 (φ.symm w)
  have hψker : ψ.ker = (GLBPrimeCore p H).subgroupOf W := by
    ext w
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    have h1 : ψ w = 1 ↔ φ.symm w ∈ ψH.ker := Iff.rfl
    rw [h1, hψ2, Subgroup.mem_subgroupOf, MonoidHom.mem_ker, ← hφ w]
    exact (mem_glbPrimeCore_iff_mk_eq_one _).symm
  have hplace₀ : ∀ w : W, (w : G) = c₀ → (ψ w).2 = 1 := by
    intro w hw
    have hy : ((φ.symm w : WH) : H) = c₀' := Subtype.ext (by rw [hφ, hw])
    rw [← AltData.altPairEquiv_mem_left_iff Mo.card₁ Mo.card₂ Mo.disjoint (ψ w), hψdef w, hy,
      hc₀π]
    exact Mo.ι_a₁_mem hodd (hK.elem.2 _ Mo.mem₁)
  have hplace₁ : ∀ w : W, (w : G) = c₁ → (ψ w).1 = 1 := by
    intro w hw
    have hy : ((φ.symm w : WH) : H) = c₁' := Subtype.ext (by rw [hφ, hw])
    rw [← AltData.altPairEquiv_mem_right_iff Mo.card₁ Mo.card₂ Mo.disjoint (ψ w), hψdef w, hy,
      hc₁π]
    exact Mo.ι_a₂_mem hodd (hK.elem.2 _ Mo.mem₂)
  have hkO' : ∀ x, x ∈ Mo.O₂ ↔ Mo.ι k x ∈ Mo.O₁ := fun x => by
    have := hkO x
    have := Mo.mem₂_iff x
    have := Mo.mem₂_iff (Mo.ι k x)
    tauto
  have hswap : ∀ w w' : W, (w' : G) = s * w * s⁻¹ →
      ((ψ w).2 = 1 → (ψ w').1 = 1) ∧ ((ψ w).1 = 1 → (ψ w').2 = 1) := by
    intro w w' hww'
    have hy' : ((φ.symm w' : WH) : H) = t * ((φ.symm w : WH) : H) * t⁻¹ :=
      Subtype.ext (by simp [hφ, hww', s])
    have hιy' : Mo.ι (π ((φ.symm w' : WH) : H)) =
        Mo.ι k * Mo.ι (π ((φ.symm w : WH) : H)) * (Mo.ι k)⁻¹ := by
      rw [hy', hπt, map_mul, map_mul, map_inv]
    constructor
    · intro h2
      have h1 : Mo.ι (π ((φ.symm w : WH) : H)) ∈ altOn Mo.O₁ := by
        rw [← hψdef w]
        exact (AltData.altPairEquiv_mem_left_iff Mo.card₁ Mo.card₂ Mo.disjoint (ψ w)).mpr h2
      rw [← AltData.altPairEquiv_mem_right_iff Mo.card₁ Mo.card₂ Mo.disjoint (ψ w'), hψdef w',
        hιy']
      exact conj_mem_altOn hkO h1
    · intro h1
      have h2 : Mo.ι (π ((φ.symm w : WH) : H)) ∈ altOn Mo.O₂ := by
        rw [← hψdef w]
        exact (AltData.altPairEquiv_mem_right_iff Mo.card₁ Mo.card₂ Mo.disjoint (ψ w)).mpr h1
      rw [← AltData.altPairEquiv_mem_left_iff Mo.card₁ Mo.card₂ Mo.disjoint (ψ w'), hψdef w',
        hιy']
      exact conj_mem_altOn hkO' h2
  exact ⟨c₀, c₁, s, g, W, ψ, hscalar, hWK, hWW, hAW, hKnorm, hψsurj, hψker, hplace₀, hplace₁,
    hswap⟩

theorem D2Escape.altData_of_alt [Fact p.Prime] (h : D2Escape p P M A H R) (hglob : AGLGlobal G)
    (hRbar : (Rbar : Subgroup _) = (R.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)))
    (hK : D2AlmostSimple p _ Rbar ((A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)))
      (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p))) K)
    (e : K ≃* alternatingGroup (Fin (2 * p))) (hp5 : 5 ≤ p) : D2AltData p M H R A := by
  have hp : p.Prime := h.prime
  obtain ⟨c₀, c₁, s, g, W, ψ, hsc, hperf⟩ := h.perfect_of_alt hK e hp5
  obtain ⟨hD, hC⟩ := d2AltSurvivorFacts (H ⧸ primeComplementCore (G := H) p) p hp5 Rbar _ _ K hK
    ⟨e⟩
  have hsurv := h.survivorData_of_reduced hglob hD (hRbar ▸ hC)
  have hRA := hK.sylow_eq_of_alternating hp5 e
  rw [hRbar] at hRA
  have hAR : A = R := by
    refine Subgroup.eq_of_le_of_card_ge h.A_le ?_
    rw [← h.card_map_eq le_rfl, ← h.card_map_eq h.A_le, hRA]
  refine ⟨hsurv.pair, hp5, hAR, h.elem, h.card_A, ⟨c₀, c₁, s, g, hsc⟩, hsurv.normal_dichotomy, ?_,
    hsurv.centralizer_le, pRank_inf_le_of_pRank_top_le hp hK.pRank_top_eq.le,
    ⟨c₀, c₁, s, g, W, ψ, hsc, hperf⟩⟩
  intro Y hY hYn hYp
  obtain ⟨Mo⟩ := hK.nonempty_altModel hp5 e
  exact le_glbPrimeCore_of_map_eq_bot (hY.trans inf_le_left)
    (hK.eq_bot_of_isPGroup hp5 Mo (Subgroup.map_mono (Subgroup.subgroupOf_mono H hY))
      (map_mk_le_normalizer_map_mk hYn) (isPGroup_map_of_forall_pow_mem hYp))

end CFSG.AGLEmbeddingD2
