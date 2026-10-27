module

public import Mathlib.GroupTheory.Nilpotent

public section

namespace CFSG.LocalAnalysis.GLTheoremB.Prop95I1921

theorem exists_pow_two_pow_eq_of_central {G : Type*} [Group G] [Finite G] {Z : Subgroup G}
    (hZc : Z ≤ Subgroup.center G) (hZ : ∀ z ∈ Z, ∀ n : ℕ, z ^ (2 ^ n) = 1 → z = 1)
    (m : ℕ) {z₀ : G} (hz₀ : z₀ ∈ Z) : ∃ z ∈ Z, z ^ (2 ^ m) = z₀ := by
  let f : Z → Z := fun y => y ^ (2 ^ m)
  have hinj : Function.Injective f := by
    intro y₁ y₂ h
    have hc : Commute (y₁ : G) (y₂ : G)⁻¹ :=
      (Subgroup.mem_center_iff.1 (hZc y₁.2) (y₂ : G)⁻¹).symm
    have h' : (y₁ : G) ^ (2 ^ m) = (y₂ : G) ^ (2 ^ m) := by
      simpa [f] using congrArg Subtype.val h
    have h1 : ((y₁ : G) * (y₂ : G)⁻¹) ^ (2 ^ m) = 1 := by
      rw [hc.mul_pow, inv_pow, h', mul_inv_cancel]
    have h2 : (y₁ : G) * (y₂ : G)⁻¹ = 1 := hZ _ (Z.mul_mem y₁.2 (Z.inv_mem y₂.2)) m h1
    exact Subtype.ext (mul_inv_eq_one.1 h2)
  obtain ⟨y, hy⟩ := Finite.injective_iff_surjective.1 hinj ⟨z₀, hz₀⟩
  refine ⟨y, y.2, ?_⟩
  simpa [f] using congrArg Subtype.val hy

theorem exists_subgroup_two_elements {G : Type*} [Group G] [Finite G] {H Z : Subgroup G}
    (hZc : Z ≤ Subgroup.center G) (hH : ∀ h ∈ H, ∃ n : ℕ, h ^ (2 ^ n) ∈ Z) :
    ∃ V : Subgroup G, ∀ g : G, g ∈ V ↔ g ∈ H ∧ ∃ n : ℕ, g ^ (2 ^ n) = 1 := by
  let N : Subgroup ↥H := Z.subgroupOf H
  have hNc : N ≤ Subgroup.center ↥H := by
    intro n hn
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_center_iff.1 (hZc (Subgroup.mem_subgroupOf.1 hn)) (g : G))
  haveI hNn : N.Normal := Subgroup.normal_of_le_center hNc
  have hQ2 : IsPGroup 2 (↥H ⧸ N) := by
    intro q
    refine QuotientGroup.induction_on q ?_
    intro g
    obtain ⟨n, hn⟩ := hH g g.2
    refine ⟨n, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact Subgroup.mem_subgroupOf.2 (by simpa using hn)
  haveI : Group.IsNilpotent (↥H ⧸ N) := hQ2.isNilpotent
  haveI : Group.IsNilpotent ↥H := Subgroup.isNilpotent_of_ker_le_center (QuotientGroup.mk' N)
    (by rw [QuotientGroup.ker_mk']; exact hNc)
  let S : Sylow 2 ↥H := default
  haveI hSn : S.Normal := inferInstance
  haveI : Finite (Sylow 2 ↥H) := inferInstance
  haveI : Unique (Sylow 2 ↥H) := Sylow.unique_of_normal S hSn
  refine ⟨(S : Subgroup ↥H).map H.subtype, fun g => ?_⟩
  constructor
  · rintro ⟨s, hs, rfl⟩
    refine ⟨s.2, ?_⟩
    obtain ⟨n, hn⟩ := S.isPGroup' ⟨s, hs⟩
    refine ⟨n, ?_⟩
    simpa using congrArg (fun y : ↥(S : Subgroup ↥H) => (((y : ↥H)) : G)) hn
  · rintro ⟨hgH, n, hn⟩
    let g' : ↥H := ⟨g, hgH⟩
    have hg'n : g' ^ (2 ^ n) = 1 := Subtype.ext (by simpa [g'] using hn)
    have hP : IsPGroup 2 (Subgroup.zpowers g') :=
      IsPGroup.of_card_dvd_pow (n := n) (by
        rw [Nat.card_zpowers]
        exact orderOf_dvd_of_pow_eq_one hg'n)
    obtain ⟨S', hS'⟩ := hP.exists_le_sylow
    have hS'S : S' = S := Subsingleton.elim _ _
    have hg'S : g' ∈ (S : Subgroup ↥H) := by
      have := hS' (Subgroup.mem_zpowers g')
      rw [hS'S] at this
      exact this
    exact ⟨g', hg'S, rfl⟩

theorem exists_normal_two_lift {X : Type} [Group X] [Finite X] {K : Subgroup X} {x : X}
    (hxN : x ∈ Subgroup.normalizer (K : Set X))
    (hZ : ∀ z ∈ Subgroup.center ↥K, ∀ n : ℕ, z ^ (2 ^ n) = 1 → z = 1)
    (E : Subgroup (↥K ⧸ Subgroup.center ↥K)) (hE2 : ∀ ε ∈ E, ∃ n : ℕ, ε ^ (2 ^ n) = 1)
    (hEx : ∀ a : ↥K, (QuotientGroup.mk a : ↥K ⧸ Subgroup.center ↥K) ∈ E →
      (QuotientGroup.mk (K.normalizerMonoidHom ⟨x, hxN⟩ a) : ↥K ⧸ Subgroup.center ↥K) =
        QuotientGroup.mk a)
    (hEn : ∀ c : ↥K, (c : X) ∈ Subgroup.centralizer ({x} : Set X) → ∀ ε ∈ E,
      (QuotientGroup.mk c : ↥K ⧸ Subgroup.center ↥K) * ε * (QuotientGroup.mk c)⁻¹ ∈ E) :
    ∃ Q : Subgroup X, Q ≤ K ∧ Q ≤ Subgroup.centralizer ({x} : Set X) ∧
      (∀ q ∈ Q, ∃ n : ℕ, q ^ (2 ^ n) = 1) ∧
      (∀ c ∈ K ⊓ Subgroup.centralizer ({x} : Set X), ∀ q ∈ Q, c * q * c⁻¹ ∈ Q) ∧
      ∀ ε ∈ E, ∃ q : ↥K, (q : X) ∈ Q ∧
        (QuotientGroup.mk q : ↥K ⧸ Subgroup.center ↥K) = ε := by
  classical
  let Hc : Subgroup ↥K := E.comap (QuotientGroup.mk' (Subgroup.center ↥K))
  have hmemHc : ∀ a : ↥K,
      a ∈ Hc ↔ (QuotientGroup.mk a : ↥K ⧸ Subgroup.center ↥K) ∈ E := fun a => Iff.rfl
  have hHc : ∀ h ∈ Hc, ∃ n : ℕ, h ^ (2 ^ n) ∈ Subgroup.center ↥K := by
    intro h hh
    obtain ⟨n, hn⟩ := hE2 _ ((hmemHc h).1 hh)
    refine ⟨n, (QuotientGroup.eq_one_iff _).1 ?_⟩
    rw [QuotientGroup.mk_pow]
    exact hn
  obtain ⟨V, hV⟩ := exists_subgroup_two_elements (G := ↥K) (H := Hc)
    (Z := Subgroup.center ↥K) le_rfl hHc
  have hxV : ∀ v ∈ V, ((K.normalizerMonoidHom ⟨x, hxN⟩ v : ↥K)) = v := by
    intro v hv
    obtain ⟨hvH, n, hn⟩ := (hV v).1 hv
    have h1 : (QuotientGroup.mk (K.normalizerMonoidHom ⟨x, hxN⟩ v) :
        ↥K ⧸ Subgroup.center ↥K) = QuotientGroup.mk v := hEx v ((hmemHc v).1 hvH)
    have hzmem : v⁻¹ * K.normalizerMonoidHom ⟨x, hxN⟩ v ∈ Subgroup.center ↥K :=
      QuotientGroup.eq.1 h1.symm
    have hcomm : Commute v (v⁻¹ * K.normalizerMonoidHom ⟨x, hxN⟩ v) :=
      Subgroup.mem_center_iff.1 hzmem v
    have hw : K.normalizerMonoidHom ⟨x, hxN⟩ v =
        v * (v⁻¹ * K.normalizerMonoidHom ⟨x, hxN⟩ v) := (mul_inv_cancel_left _ _).symm
    have hw1 : (K.normalizerMonoidHom ⟨x, hxN⟩ v) ^ (2 ^ n) = 1 := by
      rw [← map_pow, hn, map_one]
    have hz1 : (v⁻¹ * K.normalizerMonoidHom ⟨x, hxN⟩ v) ^ (2 ^ n) = 1 := by
      have h2 := hw1
      rw [hw, hcomm.mul_pow, hn, one_mul] at h2
      exact h2
    have hz := hZ _ hzmem n hz1
    rw [hw, hz, mul_one]
  refine ⟨V.map K.subtype, Subgroup.map_subtype_le V, ?_, ?_, ?_, ?_⟩
  ·
    intro q hq
    obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.1 hq
    have h1 := congrArg (fun y : ↥K => (y : X)) (hxV v hv)
    have h2 : x * (v : X) * x⁻¹ = (v : X) := h1
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (mul_inv_eq_iff_eq_mul.1 h2).symm
  ·
    intro q hq
    obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.1 hq
    obtain ⟨_, n, hn⟩ := (hV v).1 hv
    exact ⟨n, by simpa using congrArg Subtype.val hn⟩
  ·
    intro c hc q hq
    obtain ⟨hcK, hcC⟩ := Subgroup.mem_inf.1 hc
    obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.1 hq
    obtain ⟨hvH, n, hn⟩ := (hV v).1 hv
    let c' : ↥K := ⟨c, hcK⟩
    have hmem : c' * v * c'⁻¹ ∈ V := by
      refine (hV _).2 ⟨?_, n, ?_⟩
      · rw [hmemHc, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
        exact hEn c' hcC _ ((hmemHc v).1 hvH)
      · rw [conj_pow, hn, mul_one, mul_inv_cancel]
    exact Subgroup.mem_map.2 ⟨c' * v * c'⁻¹, hmem, rfl⟩
  ·
    intro ε hε
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective ε
    obtain ⟨m, hm⟩ := hE2 _ hε
    have ha : a ^ (2 ^ m) ∈ Subgroup.center ↥K := by
      refine (QuotientGroup.eq_one_iff _).1 ?_
      rw [QuotientGroup.mk_pow]
      exact hm
    obtain ⟨z, hz, hzm⟩ := exists_pow_two_pow_eq_of_central (Z := Subgroup.center ↥K) le_rfl hZ m
      ((Subgroup.center ↥K).inv_mem ha)
    have hcomm : Commute a z := Subgroup.mem_center_iff.1 hz a
    have hq1 : (a * z) ^ (2 ^ m) = 1 := by
      rw [hcomm.mul_pow, hzm, mul_inv_cancel]
    have hmk : (QuotientGroup.mk (a * z) : ↥K ⧸ Subgroup.center ↥K) = QuotientGroup.mk a := by
      rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff z).2 hz, mul_one]
    have hqH : a * z ∈ Hc := (hmemHc _).2 (by rw [hmk]; exact hε)
    exact ⟨a * z, Subgroup.mem_map.2 ⟨a * z, (hV _).2 ⟨hqH, m, hq1⟩, rfl⟩, hmk⟩

end CFSG.LocalAnalysis.GLTheoremB.Prop95I1921
