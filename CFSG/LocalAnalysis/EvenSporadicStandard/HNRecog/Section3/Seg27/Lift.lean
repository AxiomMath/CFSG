module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Generic

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

private lemma seg27_eq_of_mem_commutator_of_theta_eq {H : Type} [Group H]
    {θ : H →* Equiv.Perm (Fin 8)} (φ : alternatingGroup (Fin 8) ≃* ↥(_root_.commutator H))
    (hθ : ∀ g, θ (φ g : H) = (g : Equiv.Perm (Fin 8)))
    {x y : H} (hx : x ∈ _root_.commutator H) (hy : y ∈ _root_.commutator H)
    (h : θ x = θ y) : x = y := by
  obtain ⟨g₀, hg₀⟩ : ∃ g : alternatingGroup (Fin 8), (φ g : H) = x :=
    ⟨φ.symm ⟨x, hx⟩, by simp⟩
  obtain ⟨g₁, hg₁⟩ : ∃ g : alternatingGroup (Fin 8), (φ g : H) = y :=
    ⟨φ.symm ⟨y, hy⟩, by simp⟩
  have hgg : g₀ = g₁ :=
    Subtype.ext (by rw [← hθ g₀, ← hθ g₁, hg₀, hg₁]; exact h)
  rw [← hg₀, ← hg₁, hgg]

private lemma seg27_zpowers_eq_pair {H : Type} [Group H] {a : H} (ha : a * a = 1) :
    (Subgroup.zpowers a : Set H) = {1, a} := by
  ext x
  constructor
  · intro hx
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    obtain ⟨k, rfl | rfl⟩ := Int.even_or_odd' n
    · rw [zpow_mul, show a ^ (2 : ℤ) = 1 by rw [zpow_two, ha], one_zpow]
      simp
    · rw [zpow_add, zpow_mul, show a ^ (2 : ℤ) = 1 by rw [zpow_two, ha], one_zpow,
        zpow_one, one_mul]
      simp
  · rintro (h | h)
    · rw [h]; exact Subgroup.one_mem _
    · rw [h]; exact Subgroup.mem_zpowers a

private lemma seg27_orderOf_two_of_mem_of_theta {H : Type} [Group H]
    {θ : H →* Equiv.Perm (Fin 8)} (hker : θ.ker = Subgroup.center H)
    {a b : H} {K₀ K₁ : Subgroup H}
    (hK₀ : K₀ ⊓ Subgroup.center H = Subgroup.zpowers a)
    (hK₁ : K₁ ⊓ Subgroup.center H = Subgroup.zpowers b)
    (hdisj : Subgroup.zpowers a ⊓ Subgroup.zpowers b = ⊥)
    {s : Equiv.Perm (Fin 8)} (hs : orderOf s = 2)
    {k : H} (hk : k ∈ K₀ ⊓ K₁) (hθk : θ k = s) : orderOf k = 2 := by
  have hkne : k ≠ 1 := by
    intro h1
    rw [h1, map_one] at hθk
    have hs1 : s = 1 := hθk.symm
    rw [hs1, orderOf_one] at hs
    exact absurd hs (by decide)
  have hkk : k * k = 1 := by
    have hcenter : k * k ∈ Subgroup.center H := by
      have hker' : k * k ∈ θ.ker := by
        rw [MonoidHom.mem_ker, map_mul, hθk]
        have h2 : s ^ orderOf s = 1 := pow_orderOf_eq_one s
        rw [hs] at h2
        simpa [pow_two] using h2
      rwa [hker] at hker'
    have hmem : k * k ∈ Subgroup.zpowers a ⊓ Subgroup.zpowers b := by
      refine ⟨?_, ?_⟩
      · have h1 : k * k ∈ K₀ ⊓ Subgroup.center H := ⟨K₀.mul_mem hk.1 hk.1, hcenter⟩
        rwa [hK₀] at h1
      · have h2 : k * k ∈ K₁ ⊓ Subgroup.center H := ⟨K₁.mul_mem hk.2 hk.2, hcenter⟩
        rwa [hK₁] at h2
    have hbot : k * k ∈ (⊥ : Subgroup H) := by
      rw [← hdisj]; exact hmem
    simpa using hbot
  exact orderOf_eq_prime (by rw [pow_two]; exact hkk) hkne

theorem seg27_lift_comm {H : Type} [Group H] {θ : H →* Equiv.Perm (Fin 8)}
    (φ : alternatingGroup (Fin 8) ≃* ↥(_root_.commutator H))
    (hθ : ∀ g, θ (φ g : H) = (g : Equiv.Perm (Fin 8)))
    {L₀ L₁ : Subgroup H} (h₀ : L₀ ≤ _root_.commutator H) (h₁ : L₁ ≤ _root_.commutator H)
    {s : Equiv.Perm (Fin 8)} (hs₀ : s ∈ L₀.map θ) (hs₁ : s ∈ L₁.map θ) (hs : orderOf s = 2) :
    ∃ k ∈ L₀ ⊓ L₁, orderOf k = 2 := by
  obtain ⟨l₀, hl₀, hθl₀⟩ := Subgroup.mem_map.mp hs₀
  obtain ⟨l₁, hl₁, hθl₁⟩ := Subgroup.mem_map.mp hs₁
  have hcomm₀ : l₀ ∈ _root_.commutator H := h₀ hl₀
  have hcomm₁ : l₁ ∈ _root_.commutator H := h₁ hl₁
  have hll : l₀ = l₁ :=
    seg27_eq_of_mem_commutator_of_theta_eq φ hθ hcomm₀ hcomm₁ (hθl₀.trans hθl₁.symm)
  have hkk : l₀ * l₀ = 1 := by
    apply seg27_eq_of_mem_commutator_of_theta_eq φ hθ
      (Subgroup.mul_mem _ hcomm₀ hcomm₀) (Subgroup.one_mem _)
    rw [map_mul, map_one, hθl₀]
    have h2 : s ^ orderOf s = 1 := pow_orderOf_eq_one s
    rw [hs] at h2
    simpa [pow_two] using h2
  have hkne : l₀ ≠ 1 := by
    intro h1
    rw [h1, map_one] at hθl₀
    have hs1 : s = 1 := hθl₀.symm
    rw [hs1, orderOf_one] at hs
    exact absurd hs (by decide)
  exact ⟨l₀, ⟨hl₀, hll ▸ hl₁⟩, orderOf_eq_prime (by rw [pow_two]; exact hkk) hkne⟩

theorem seg27_lift_center {H : Type} [Group H] {θ : H →* Equiv.Perm (Fin 8)}
    (hker : θ.ker = Subgroup.center H) {a b : H}
    (hZ : (Subgroup.center H : Set H) = {1, a, b, a * b})
    (hsq : ∀ z ∈ Subgroup.center H, z * z = 1) (hab : a ≠ b) {K₀ K₁ : Subgroup H}
    (hK₀ : K₀ ⊓ Subgroup.center H = Subgroup.zpowers a)
    (hK₁ : K₁ ⊓ Subgroup.center H = Subgroup.zpowers b)
    {s : Equiv.Perm (Fin 8)} (hs₀ : s ∈ K₀.map θ) (hs₁ : s ∈ K₁.map θ) (hs : orderOf s = 2) :
    ∃ k ∈ K₀ ⊓ K₁, orderOf k = 2 := by
  have ha_center : a ∈ Subgroup.center H := by
    have h : a ∈ (Subgroup.center H : Set H) := by rw [hZ]; simp
    exact h
  have hb_center : b ∈ Subgroup.center H := by
    have h : b ∈ (Subgroup.center H : Set H) := by rw [hZ]; simp
    exact h
  have ha2 : a * a = 1 := hsq a ha_center
  have hb2 : b * b = 1 := hsq b hb_center
  have ha_K₀ : a ∈ K₀ := by
    have h : a ∈ K₀ ⊓ Subgroup.center H := by rw [hK₀]; exact Subgroup.mem_zpowers a
    exact h.1
  have hb_K₁ : b ∈ K₁ := by
    have h : b ∈ K₁ ⊓ Subgroup.center H := by rw [hK₁]; exact Subgroup.mem_zpowers b
    exact h.1
  have hθa : θ a = 1 := by
    have h : a ∈ θ.ker := by rw [hker]; exact ha_center
    exact MonoidHom.mem_ker.mp h
  have hθb : θ b = 1 := by
    have h : b ∈ θ.ker := by rw [hker]; exact hb_center
    exact MonoidHom.mem_ker.mp h
  have hdisj : Subgroup.zpowers a ⊓ Subgroup.zpowers b = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxa, hxb⟩ := Subgroup.mem_inf.mp hx
    have hxa' : x ∈ ({1, a} : Set H) := by
      rw [← seg27_zpowers_eq_pair ha2]; exact hxa
    have hxb' : x ∈ ({1, b} : Set H) := by
      rw [← seg27_zpowers_eq_pair hb2]; exact hxb
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hxa' hxb'
    rcases hxa' with rfl | rfl
    · simp
    · rcases hxb' with h | h
      · rw [h]; simp
      · exact absurd h hab
  obtain ⟨k₀, hk₀K, hθk₀⟩ := Subgroup.mem_map.mp hs₀
  obtain ⟨k₁, hk₁K, hθk₁⟩ := Subgroup.mem_map.mp hs₁
  have hmem_ker : k₀⁻¹ * k₁ ∈ θ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hθk₀, hθk₁, inv_mul_cancel]
  have hmem_center : k₀⁻¹ * k₁ ∈ Subgroup.center H := by
    rwa [hker] at hmem_ker
  have hset : k₀⁻¹ * k₁ ∈ ({1, a, b, a * b} : Set H) := by
    rw [← hZ]; exact hmem_center
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hset
  rcases hset with h | h | h | h
  · have hk₁eq : k₁ = k₀ := by
      calc k₁ = (k₀ * k₀⁻¹) * k₁ := by rw [mul_inv_cancel, one_mul]
        _ = k₀ * (k₀⁻¹ * k₁) := by rw [mul_assoc]
        _ = k₀ * 1 := by rw [h]
        _ = k₀ := mul_one _
    exact ⟨k₀, ⟨hk₀K, hk₁eq ▸ hk₁K⟩,
      seg27_orderOf_two_of_mem_of_theta hker hK₀ hK₁ hdisj hs ⟨hk₀K, hk₁eq ▸ hk₁K⟩ hθk₀⟩
  · have hk₁eq : k₁ = k₀ * a := by
      calc k₁ = (k₀ * k₀⁻¹) * k₁ := by rw [mul_inv_cancel, one_mul]
        _ = k₀ * (k₀⁻¹ * k₁) := by rw [mul_assoc]
        _ = k₀ * a := by rw [h]
    have hmem : k₁ ∈ K₀ ⊓ K₁ := ⟨by rw [hk₁eq]; exact K₀.mul_mem hk₀K ha_K₀, hk₁K⟩
    exact ⟨k₁, hmem,
      seg27_orderOf_two_of_mem_of_theta hker hK₀ hK₁ hdisj hs hmem hθk₁⟩
  · have hk₁eq : k₁ = k₀ * b := by
      calc k₁ = (k₀ * k₀⁻¹) * k₁ := by rw [mul_inv_cancel, one_mul]
        _ = k₀ * (k₀⁻¹ * k₁) := by rw [mul_assoc]
        _ = k₀ * b := by rw [h]
    have hkeq : k₀ = k₁ * b⁻¹ := by
      rw [hk₁eq, mul_assoc k₀ b b⁻¹, mul_inv_cancel, mul_one]
    have hmem : k₀ ∈ K₀ ⊓ K₁ :=
      ⟨hk₀K, by rw [hkeq]; exact K₁.mul_mem hk₁K (K₁.inv_mem hb_K₁)⟩
    exact ⟨k₀, hmem,
      seg27_orderOf_two_of_mem_of_theta hker hK₀ hK₁ hdisj hs hmem hθk₀⟩
  · have hk₁eq : k₁ = (k₀ * a) * b := by
      calc k₁ = (k₀ * k₀⁻¹) * k₁ := by rw [mul_inv_cancel, one_mul]
        _ = k₀ * (k₀⁻¹ * k₁) := by rw [mul_assoc]
        _ = k₀ * (a * b) := by rw [h]
        _ = (k₀ * a) * b := by rw [mul_assoc]
    have hkeq : k₀ * a = k₁ * b⁻¹ := by
      rw [hk₁eq, mul_assoc (k₀ * a) b b⁻¹, mul_inv_cancel, mul_one]
    have hmem : k₀ * a ∈ K₀ ⊓ K₁ :=
      ⟨K₀.mul_mem hk₀K ha_K₀,
        by rw [hkeq]; exact K₁.mul_mem hk₁K (K₁.inv_mem hb_K₁)⟩
    exact ⟨k₀ * a, hmem,
      seg27_orderOf_two_of_mem_of_theta hker hK₀ hK₁ hdisj hs hmem
        (by rw [map_mul, hθk₀, hθa, mul_one])⟩

theorem seg27_card_map_mul {H : Type} [Group H] [Finite H] (θ : H →* Equiv.Perm (Fin 8))
    (K : Subgroup H) : Nat.card (K.map θ) * Nat.card (K ⊓ θ.ker : Subgroup H) = Nat.card K := by
  rw [← Subgroup.relIndex_ker K θ]
  simpa [inf_comm] using (Subgroup.relIndex_mul_card (H := θ.ker) (K := K))

theorem seg27_nonempty_mulEquiv_map {H : Type} [Group H] {θ : H →* Equiv.Perm (Fin 8)}
    (φ : alternatingGroup (Fin 8) ≃* ↥(_root_.commutator H))
    (hθ : ∀ g, θ (φ g : H) = (g : Equiv.Perm (Fin 8)))
    {L : Subgroup H} (hL : L ≤ _root_.commutator H) : Nonempty (↥L ≃* ↥(L.map θ)) := by
  have hinj : Function.Injective (θ.domRestrict L) := by
    intro x y hxy
    apply Subtype.ext
    apply seg27_eq_of_mem_commutator_of_theta_eq φ hθ (hL x.2) (hL y.2)
    simpa using hxy
  exact ⟨(MulEquiv.ofBijective (θ.domRestrict L).rangeRestrict
    ⟨(MonoidHom.rangeRestrict_injective_iff).mpr hinj,
      MonoidHom.rangeRestrict_surjective _⟩).trans
    (MulEquiv.subgroupCongr (MonoidHom.domRestrict_range L θ))⟩

theorem seg27_hasSixOrbit_iff {H : Type} [Group H] {θ : H →* Equiv.Perm (Fin 8)}
    (φ : alternatingGroup (Fin 8) ≃* ↥(_root_.commutator H))
    (hθ : ∀ g, θ (φ g : H) = (g : Equiv.Perm (Fin 8)))
    {L : Subgroup H} (hL : L ≤ _root_.commutator H) :
    HasSixOrbit φ L ↔ ∃ o : Fin 8, (MulAction.orbit (L.map θ) o).ncard = 6 := by
  have hset : ∀ x : Fin 8,
      {j : Fin 8 | ∃ g : alternatingGroup (Fin 8), (φ g : H) ∈ L ∧
        (g : Equiv.Perm (Fin 8)) x = j} = MulAction.orbit (L.map θ) x := by
    intro x
    ext j
    constructor
    · rintro ⟨g, hgL, hgj⟩
      rw [MulAction.mem_orbit_iff]
      refine ⟨⟨(g : Equiv.Perm (Fin 8)), ?_⟩, ?_⟩
      · exact Subgroup.mem_map.mpr ⟨(φ g : H), hgL, hθ g⟩
      · rw [Subgroup.mk_smul, Equiv.Perm.smul_def]
        exact hgj
    · intro hj
      rw [MulAction.mem_orbit_iff] at hj
      obtain ⟨m, hm⟩ := hj
      obtain ⟨l, hlL, hlθ⟩ := Subgroup.mem_map.mp m.2
      obtain ⟨g, hg⟩ : ∃ g : alternatingGroup (Fin 8), (φ g : H) = l :=
        ⟨φ.symm ⟨l, hL hlL⟩, by simp⟩
      refine ⟨g, ?_, ?_⟩
      · rw [hg]; exact hlL
      · have hgm : (g : Equiv.Perm (Fin 8)) = (m : Equiv.Perm (Fin 8)) := by
          rw [← hθ g, hg, hlθ]
        have hmx : (m : Equiv.Perm (Fin 8)) x = j := by
          simpa [Subgroup.smul_def] using hm
        rw [hgm]; exact hmx
  unfold HasSixOrbit
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨i, by rw [← hset i]; exact hi⟩
  · rintro ⟨o, ho⟩
    exact ⟨o, by rw [hset o]; exact ho⟩

theorem seg27_derivedOf_le_commutator {H : Type} [Group H] (K : Subgroup H) :
    derivedOf K ≤ _root_.commutator H := by
  rw [derivedOf, _root_.commutator_def, Subgroup.map_commutator]
  have htop : (⊤ : Subgroup ↥K).map K.subtype = K := by
    ext x
    constructor
    · rintro ⟨y, -, rfl⟩
      exact y.2
    · intro hx
      exact ⟨⟨x, hx⟩, trivial, rfl⟩
  rw [htop, _root_.commutator_def]
  exact Subgroup.commutator_mono le_top le_top

theorem seg27_isShapeA6_derivedOf {H : Type} [Group H] {K : Subgroup H}
    (hK : IsShapeZ2TimesSym 6 ↥K) : Nonempty (↥(derivedOf K) ≃* alternatingGroup (Fin 6)) := by
  classical
  obtain ⟨e⟩ := hK
  have hZ : (⁅(⊤ : Subgroup (Z 2)), ⊤⁆ : Subgroup (Z 2)) = ⊥ := by
    rw [← _root_.commutator_def]
    exact (commutator_eq_bot_iff (Z 2)).mpr inferInstance
  have hS : (⁅(⊤ : Subgroup (Sym 6)), ⊤⁆ : Subgroup (Sym 6)) =
      alternatingGroup (Fin 6) := by
    rw [← _root_.commutator_def]
    exact alternatingGroup.commutator_perm_eq (α := Fin 6) (by simp)
  have hcomm : _root_.commutator (Z 2 × Sym 6) =
      (⊥ : Subgroup (Z 2)).prod (alternatingGroup (Fin 6)) := by
    rw [_root_.commutator_def, ← Subgroup.top_prod_top (G := Z 2) (N := Sym 6),
      Subgroup.commutator_prod_prod, hZ, hS]
  have hgmap : (_root_.commutator ↥K).map e.toMonoidHom = _root_.commutator (Z 2 × Sym 6) := by
    rw [_root_.commutator_def, _root_.commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ e.surjective]
  let eK : ↥(derivedOf K) ≃* ↥(_root_.commutator ↥K) :=
    (Subgroup.equivMapOfInjective (_root_.commutator ↥K) K.subtype K.subtype_injective).symm
  have iso1 : ↥(derivedOf K) ≃* ↥(alternatingGroup (Fin 6)) :=
    eK.trans <|
      (Subgroup.equivMapOfInjective (_root_.commutator ↥K) e.toMonoidHom e.injective).trans <|
      (MulEquiv.subgroupCongr hgmap).trans <|
      (MulEquiv.subgroupCongr hcomm).trans <|
      (Subgroup.prodEquiv (⊥ : Subgroup (Z 2)) (alternatingGroup (Fin 6))).trans <|
      MulEquiv.uniqueProd
  exact ⟨iso1⟩

end CFSG.EvenSporadicStandard.HNRecog.Section3
