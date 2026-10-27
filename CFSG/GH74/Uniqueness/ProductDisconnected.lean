module

public import CFSG.GH74.Uniqueness.Elements
public import CFSG.GH74.Uniqueness.Dihedral

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

section PD

variable {X : Type*} [Group X] {Z : Set X} {M : Subgroup X}

theorem IsProductDisconnected.ne_top (h : IsProductDisconnected Z M) : M ≠ ⊤ := h.1

theorem IsProductDisconnected.mem_of_conj_mem (h : IsProductDisconnected Z M) {z : X}
    (hz : z ∈ Z) (hzM : z ∈ M) {g : X} (hg : g⁻¹ * z * g ∈ M) : g ∈ M :=
  (h.2.2.1 z hz hzM g).mp hg

theorem IsInvariantInvolutionSet.orderOf_eq {Z : Set X} (hZ : IsInvariantInvolutionSet Z) {z : X}
    (hz : z ∈ Z) : orderOf z = 2 := hZ.1 z hz

theorem IsProductDisconnected.mem_uniqU [Finite X] (hZ : IsInvariantInvolutionSet Z)
    (h : IsProductDisconnected Z M) {z : X} (hz : z ∈ Z) (hzM : z ∈ M) : z ∈ uniqU M 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact (mem_uniqU_iff 2).mpr ⟨hZ.1 z hz, hzM, fun _ hg => h.mem_of_conj_mem hz hzM hg⟩

theorem IsProductDisconnected.mem_uniqC (h : IsProductDisconnected Z M) {u : X}
    (hu : u ∈ productInvolutions Z) (huM : u ∈ M) : u ∈ uniqC M 2 :=
  ⟨hu.1, huM, h.2.2.2 u hu huM⟩

theorem IsProductDisconnected.exists_mem_not_mem (hZ : IsInvariantInvolutionSet Z)
    (h : IsProductDisconnected Z M) : ∃ z ∈ Z, z ∉ M := by
  obtain ⟨z, hz, hzM⟩ := h.2.1
  obtain ⟨g, hg⟩ : ∃ g : X, g ∉ M := by
    by_contra hall
    push Not at hall
    exact h.1 (eq_top_iff.mpr fun x _ => hall x)
  exact ⟨g⁻¹ * z * g, hZ.2 z hz g, fun hmem => hg (h.mem_of_conj_mem hz hzM hmem)⟩

theorem IsProductDisconnected.not_closure_le (hZ : IsInvariantInvolutionSet Z)
    (h : IsProductDisconnected Z M) : ¬ Subgroup.closure Z ≤ M := by
  intro hle
  obtain ⟨z, hz, hzM⟩ := h.exists_mem_not_mem hZ
  exact hzM (hle (Subgroup.subset_closure hz))



theorem IsProductDisconnected.centralizer_le_of_mem {Z : Set X} {M : Subgroup X}
    (h : IsProductDisconnected Z M) {z : X}
    (hz : z ∈ Z) (hzM : z ∈ M) : centralizer ({z} : Set X) ≤ M := by
  intro g hg
  apply h.mem_of_conj_mem hz hzM (g := g)
  have : g⁻¹ * z * g = z := by
    rw [Subgroup.mem_centralizer_singleton_iff] at hg
    rw [mul_assoc, ← hg]
    group
  rwa [this]

theorem IsProductDisconnected.restrict_of_mem (h : IsProductDisconnected Z M) {H : Subgroup X}
    {z : X} (hz : z ∈ Z) (hzH : z ∈ H) (hzM : z ∈ M) (hHM : ¬ H ≤ M) :
    IsProductDisconnected {l : H | (l : X) ∈ Z} (M.comap H.subtype) := by
  refine ⟨fun htop => hHM fun x hx => ?_, ⟨⟨z, hzH⟩, hz, hzM⟩, fun z hz hzM g => ?_,
    fun u hu huM l hl => ?_⟩
  · have : (⟨x, hx⟩ : H) ∈ M.comap H.subtype := htop ▸ Subgroup.mem_top _
    exact this
  · exact h.2.2.1 (z : X) hz hzM (g : X)
  · obtain ⟨hu2, x, hx, y, hy, hxy, rfl⟩ := hu
    have hu' : ((x * y : H) : X) ∈ productInvolutions Z := by
      refine ⟨by rw [← Subgroup.orderOf_coe] at hu2; exact hu2, (x : X), hx, (y : X), hy, ?_, rfl⟩
      exact congrArg Subtype.val hxy
    have hc := h.2.2.2 _ hu' huM
    refine hc ?_
    rw [Subgroup.mem_centralizer_singleton_iff] at hl ⊢
    exact congrArg Subtype.val hl

theorem IsProductDisconnected.restrict (h : IsProductDisconnected Z M) {H : Subgroup X}
    (hZH : Z ⊆ H) (hHM : ¬ H ≤ M) :
    IsProductDisconnected {l : H | (l : X) ∈ Z} (M.comap H.subtype) := by
  obtain ⟨z, hz, hzM⟩ := h.2.1
  exact h.restrict_of_mem hz (hZH hz) hzM hHM

theorem IsInvariantInvolutionSet.restrict {Z : Set X} (hZ : IsInvariantInvolutionSet Z)
    (H : Subgroup X) : IsInvariantInvolutionSet {l : H | (l : X) ∈ Z} := by
  refine ⟨fun l hl => ?_, fun l hl g => hZ.2 l hl g⟩
  have := hZ.1 l hl
  rwa [Subgroup.orderOf_coe] at this

end PD

section Reduction

theorem S_ZD_of_S_ZD_gen (h : S_ZD_gen) : S_ZD := by
  intro X _ _ Z M hZ hPD
  have hZL : Z ⊆ Subgroup.closure Z := Subgroup.subset_closure
  have hLM : ¬ Subgroup.closure Z ≤ M := hPD.not_closure_le hZ
  refine h ↥(Subgroup.closure Z) {l | (l : X) ∈ Z} (M.comap (Subgroup.closure Z).subtype) ?_ ?_
    (hPD.restrict hZL hLM)
  · exact hZ.restrict _
  · exact Subgroup.closure_closure_coe_preimage

end Reduction


section Lemma31

variable {X : Type*} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}

omit [Finite X] in
theorem IsInvariantInvolutionSet.isPGroup_zpowers {Z : Set X}
    (hZ : IsInvariantInvolutionSet Z) {z : X} (hz : z ∈ Z) :
    IsPGroup 2 (Subgroup.zpowers z) := by
  refine IsPGroup.of_card (n := 1) ?_
  rw [Nat.card_zpowers, hZ.1 z hz, pow_one]

omit [Finite X] in
theorem IsProductDisconnected.isUniqueSubgroup_zpowers (h : IsProductDisconnected Z M) {z : X}
    (hz : z ∈ Z) (hzM : z ∈ M) : IsUniqueSubgroup M (Subgroup.zpowers z) :=
  _root_.CFSG.GH74.Uniqueness.isUniqueSubgroup_zpowers hzM fun _ hg => h.mem_of_conj_mem hz hzM hg

omit [Finite X] in
theorem IsProductDisconnected.normalizer_le (h : IsProductDisconnected Z M) {R : Subgroup X}
    (hRM : R ≤ M) {z : X} (hz : z ∈ Z) (hzR : z ∈ R) : normalizer (R : Set X) ≤ M :=
  (h.isUniqueSubgroup_zpowers hz (hRM hzR)).normalizer_le ((Subgroup.zpowers_le).mpr hzR) hRM

theorem IsProductDisconnected.exists_sylow_le (hZ : IsInvariantInvolutionSet Z)
    (h : IsProductDisconnected Z M) {H : Subgroup X} {z : X} (hz : z ∈ Z) (hzH : z ∈ H)
    (hzM : z ∈ M) : ∃ R : Sylow 2 ↥H, (R : Subgroup ↥H).map H.subtype ≤ M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨R, -, hR⟩ := (h.isUniqueSubgroup_zpowers hz hzM).exists_sylow_le 2
    ((Subgroup.zpowers_le).mpr hzH) (hZ.isPGroup_zpowers hz)
  exact ⟨R, hR⟩

theorem IsProductDisconnected.exists_sylow_normalizer_le (hZ : IsInvariantInvolutionSet Z)
    (h : IsProductDisconnected Z M) : ∃ S : Sylow 2 X, normalizer (S : Set X) ≤ M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨z, hz, hzM⟩ := h.2.1
  exact (h.isUniqueSubgroup_zpowers hz hzM).exists_sylow_normalizer_le 2
    (hZ.isPGroup_zpowers hz)

omit [Finite X] in
theorem IsProductDisconnected.zN_eq_empty (h : IsProductDisconnected Z M) {N : Subgroup X}
    (hN : N.Normal) (hNM : N ≤ M) : Z ∩ (N : Set X) = ∅ := by
  by_contra hne
  obtain ⟨z, hz, hzN⟩ := Set.nonempty_iff_ne_empty.mpr hne
  refine h.1 (eq_top_iff.mpr fun g _ => ?_)
  refine h.mem_of_conj_mem hz (hNM hzN) (g := g) ?_
  have := hN.conj_mem z hzN g⁻¹
  rw [inv_inv] at this
  exact hNM this


theorem IsProductDisconnected.odd_orderOf_mul (hZ : IsInvariantInvolutionSet Z)
    (h : IsProductDisconnected Z M) {t s : X} (ht : t ∈ Z) (htM : t ∉ M) (hs : s ∈ Z)
    (hsM : s ∈ M ∨ s * t ∈ M) : Odd (orderOf (s * t)) := by
  by_contra hodd
  have hs2 : s * s = 1 := by
    have := pow_orderOf_eq_one s
    rwa [hZ.1 s hs, pow_two] at this
  have ht2 : t * t = 1 := by
    have := pow_orderOf_eq_one t
    rwa [hZ.1 t ht, pow_two] at this
  have heven : Even (orderOf (s * t)) := Nat.not_odd_iff_even.mp hodd
  obtain ⟨m, hm⟩ := heven
  have hmpos : 0 < m := by
    have := orderOf_pos (s * t)
    omega
  obtain ⟨hv2, hv1, hsv, htv, x, hx, hxc⟩ := dihedral_even hs2 ht2 hmpos (by rw [hm]; ring)
  set v := (s * t) ^ m with hv
  have hsvZ : s * v ∈ Z := by
    rcases hxc with h1 | h1
    · rw [← h1]; exact hZ.2 s hs x
    · rw [← h1]; exact hZ.2 t ht x
  have hvorder : orderOf v = 2 := orderOf_eq_prime (by rwa [pow_two]) hv1
  have hv𝒱 : v ∈ productInvolutions Z := by
    refine ⟨hvorder, s, hs, s * v, hsvZ, ?_, ?_⟩
    · have e1 : s * (s * v) = v := by rw [← mul_assoc, hs2, one_mul]
      have e2 : (s * v) * s = v := by rw [hsv, mul_assoc, hs2, mul_one]
      rw [e1, e2]
    · rw [← mul_assoc, hs2, one_mul]
  have hvM : v ∈ M := by
    rcases hsM with hsM | hsM
    · exact h.centralizer_le_of_mem hs hsM (Subgroup.mem_centralizer_singleton_iff.mpr hsv.symm)
    · exact M.pow_mem hsM m
  have hC := h.2.2.2 v hv𝒱 hvM
  exact htM (hC (Subgroup.mem_centralizer_singleton_iff.mpr htv))

theorem IsProductDisconnected.exists_conj_mem_closure (hZ : IsInvariantInvolutionSet Z)
    (h : IsProductDisconnected Z M) {t s : X} (ht : t ∈ Z) (htM : t ∉ M) (hs : s ∈ Z)
    (hsM : s ∈ M ∨ s * t ∈ M) :
    ∃ x ∈ Z, x ∈ Subgroup.closure ({s, t} : Set X) ∧ x⁻¹ * t * x = s := by
  have hs2 : s * s = 1 := by
    have := pow_orderOf_eq_one s
    rwa [hZ.1 s hs, pow_two] at this
  have ht2 : t * t = 1 := by
    have := pow_orderOf_eq_one t
    rwa [hZ.1 t ht, pow_two] at this
  obtain ⟨x, y, hx, -, -, hyx, hxt⟩ :=
    exists_involution_conj_of_odd hs2 ht2 (h.odd_orderOf_mul hZ ht htM hs hsM)
  refine ⟨x, ?_, hx, hxt⟩
  rw [← hyx]
  exact hZ.2 t ht y

end Lemma31


section Lemma33

variable {X : Type*} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}

omit [Finite X] in
theorem IsInvariantInvolutionSet.mul_self_eq_one (hZ : IsInvariantInvolutionSet Z) {z : X}
    (hz : z ∈ Z) : z * z = 1 := by
  have := pow_orderOf_eq_one z
  rwa [hZ.1 z hz, pow_two] at this

theorem IsProductDisconnected.isConj_of_mem (hZ : IsInvariantInvolutionSet Z)
    (h : IsProductDisconnected Z M) {a b : X} (ha : a ∈ Z) (hb : b ∈ Z) : IsConj a b := by
  obtain ⟨z, hzZ, hzM⟩ := h.2.1
  obtain ⟨t₀, ht₀, ht₀M⟩ := h.exists_mem_not_mem hZ
  have hconj : ∀ t ∈ Z, t ∉ M → IsConj t z := fun t ht htM => by
    obtain ⟨x, -, -, hx⟩ := h.exists_conj_mem_closure hZ ht htM hzZ (Or.inl hzM)
    exact isConj_iff.mpr ⟨x⁻¹, by rw [← hx]; group⟩
  have hz : ∀ a ∈ Z, IsConj a z := fun a ha => by
    by_cases haM : a ∈ M
    · obtain ⟨x, -, -, hx⟩ := h.exists_conj_mem_closure hZ ht₀ ht₀M ha (Or.inl haM)
      exact (isConj_iff.mpr ⟨x, by rw [← hx]; group⟩ : IsConj a t₀).trans (hconj t₀ ht₀ ht₀M)
    · exact hconj a ha haM
  exact (hz a ha).trans (hz b hb).symm

theorem IsProductDisconnected.exists_conj_mem (hZ : IsInvariantInvolutionSet Z)
    (h : IsProductDisconnected Z M) {z y : X} (hz : z ∈ Z) (hzM : z ∈ M) (hy : y ∈ Z)
    (hyM : y ∈ M) : ∃ m ∈ M, m⁻¹ * z * m = y := by
  obtain ⟨c, hc⟩ := isConj_iff.mp (h.isConj_of_mem hZ hz hy)
  have hmem : (c⁻¹)⁻¹ * z * c⁻¹ ∈ M := by rw [inv_inv, hc]; exact hyM
  exact ⟨c⁻¹, h.mem_of_conj_mem hz hzM hmem, by rw [inv_inv, hc]⟩

omit [Finite X] in
theorem mem_normalizer_zpowers_of_conj_mem {g x : X} (h₁ : g * x * g⁻¹ ∈ Subgroup.zpowers x)
    (h₂ : g⁻¹ * x * g ∈ Subgroup.zpowers x) : g ∈ normalizer (Subgroup.zpowers x : Set X) := by
  rw [Subgroup.mem_normalizer_iff]
  intro a
  constructor
  · intro ha
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    rw [← conj_zpow]
    exact Subgroup.zpow_mem _ h₁ k
  · intro ha
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp ha
    have h1 : a = g⁻¹ * x ^ k * g := by rw [hk]; group
    have h2 : g⁻¹ * x ^ k * g = (g⁻¹ * x * g) ^ k := by
      have := conj_zpow (a := g⁻¹) (b := x) (i := k)
      simpa using this.symm
    rw [h1, h2]
    exact Subgroup.zpow_mem _ h₂ k

theorem IsProductDisconnected.eq_of_mul_mem_centralizer (hZ : IsInvariantInvolutionSet Z)
    (h : IsProductDisconnected Z M) {z s t : X} (hz : z ∈ Z) (hzM : z ∈ M) (hs : s ∈ Z)
    (ht : t ∈ Z) (htM : t ∉ M) (hst : s * t ∈ centralizer ({z} : Set X)) :
    s = t := by
  by_contra hne
  have hs2 := hZ.mul_self_eq_one hs
  have ht2 := hZ.mul_self_eq_one ht
  have ti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have si : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs2
  set x := s * t with hx
  have hx1 : x ≠ 1 := by
    intro h1
    apply hne
    rw [eq_inv_of_mul_eq_one_left h1, ti]
  have hxM : x ∈ M := h.centralizer_le_of_mem hz hzM hst
  have hodd : Odd (orderOf x) := h.odd_orderOf_mul hZ ht htM hs (Or.inr hxM)
  have hzx : x * z = z * x := Subgroup.mem_centralizer_singleton_iff.mp hst
  have htx : t * x * t⁻¹ = x⁻¹ := by
    rw [hx, ti, mul_inv_rev, ti, si, mul_assoc, mul_assoc, ht2, mul_one]
  have hinv : ∀ a ∈ Subgroup.zpowers x, t * a * t⁻¹ = a⁻¹ := by
    intro a ha
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    rw [← conj_zpow, htx, inv_zpow]
  have hzN : z ∈ normalizer (Subgroup.zpowers x : Set X) := by
    apply mem_normalizer_zpowers_of_conj_mem
    · have : z * x * z⁻¹ = x := by rw [← hzx]; group
      rw [this]; exact Subgroup.mem_zpowers x
    · have : z⁻¹ * x * z = x := by rw [mul_assoc, hzx]; group
      rw [this]; exact Subgroup.mem_zpowers x
  have htN : t ∈ normalizer (Subgroup.zpowers x : Set X) := by
    apply mem_normalizer_zpowers_of_conj_mem
    · rw [htx]; exact Subgroup.inv_mem _ (Subgroup.mem_zpowers x)
    · have : t⁻¹ * x * t = x⁻¹ := by rw [ti]; rw [ti] at htx; exact htx
      rw [this]; exact Subgroup.inv_mem _ (Subgroup.mem_zpowers x)
  obtain ⟨y, -, hy, hyt⟩ := h.exists_conj_mem_closure hZ ht htM hz (Or.inl hzM)
  have hyN : y ∈ normalizer (Subgroup.zpowers x : Set X) := by
    have : Subgroup.closure ({z, t} : Set X) ≤ normalizer (Subgroup.zpowers x : Set X) := by
      rw [Subgroup.closure_le]
      intro a ha
      rcases ha with rfl | rfl
      · exact hzN
      · exact htN
    exact this hy
  have hw : y * x * y⁻¹ ∈ Subgroup.zpowers x :=
    ((Subgroup.mem_normalizer_iff.mp hyN) x).mp (Subgroup.mem_zpowers x)
  have hcomm : (y * x * y⁻¹) * t = t * (y * x * y⁻¹) := by
    have e : x * (y⁻¹ * t * y) = (y⁻¹ * t * y) * x := by rw [hyt]; exact hzx
    calc y * x * y⁻¹ * t = y * (x * (y⁻¹ * t * y)) * y⁻¹ := by group
      _ = y * ((y⁻¹ * t * y) * x) * y⁻¹ := by rw [e]
      _ = t * (y * x * y⁻¹) := by group
  have hwinv := hinv _ hw
  have hw2 : (y * x * y⁻¹) * (y * x * y⁻¹) = 1 := by
    have h1 : t * (y * x * y⁻¹) * t⁻¹ = y * x * y⁻¹ := by rw [← hcomm]; group
    rw [h1] at hwinv
    exact mul_eq_one_iff_eq_inv.mpr hwinv
  have hord : orderOf (y * x * y⁻¹) = orderOf x := by
    simpa using orderOf_injective (MulAut.conj y).toMonoidHom (MulAut.conj y).injective x
  have hdvd : orderOf (y * x * y⁻¹) ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hw2)
  have hone : orderOf (y * x * y⁻¹) = 1 := by
    rw [hord] at hdvd ⊢
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
    · exact h1
    · rw [h2] at hodd; exact absurd hodd (by decide)
  have : y * x * y⁻¹ = 1 := orderOf_eq_one_iff.mp hone
  exact hx1 (by simpa using this)

end Lemma33


section CardConj

variable {X : Type*} [Group X]

theorem card_conjClass_mul_card_centralizer (z : X) :
    Nat.card {y : X // IsConj y z} * Nat.card (centralizer ({z} : Set X)) = Nat.card X := by
  have h1 : (centralizer ({z} : Set X)).index = (MulAction.orbit (ConjAct X) z).ncard := by
    rw [← MulAction.index_stabilizer (ConjAct X) z]
    rw [Subgroup.centralizer_eq_comap_stabilizer z]
    exact Subgroup.index_comap_of_surjective _ ConjAct.toConjAct.surjective
  have h2 : (MulAction.orbit (ConjAct X) z).ncard = Nat.card {y : X // IsConj y z} := by
    rw [← Nat.card_coe_set_eq]
    exact Nat.card_congr (Equiv.subtypeEquivRight (fun y => by simp [ConjAct.mem_orbit_conjAct]))
  rw [h2] at h1
  rw [mul_comm, ← h1]
  exact Subgroup.card_mul_index _

end CardConj

section Lemma34

variable {X : Type*} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}

omit [Finite X] in
theorem IsInvariantInvolutionSet.isConj_mem (hZ : IsInvariantInvolutionSet Z) {z y : X}
    (hz : z ∈ Z) (hy : IsConj y z) : y ∈ Z := by
  obtain ⟨c, hc⟩ := isConj_iff.mp hy.symm
  have h1 := hZ.2 z hz c⁻¹
  rwa [inv_inv, hc] at h1

theorem IsProductDisconnected.card_mul_card_centralizer (hZ : IsInvariantInvolutionSet Z)
    (h : IsProductDisconnected Z M) {z : X} (hz : z ∈ Z) :
    Nat.card Z * Nat.card (centralizer ({z} : Set X)) = Nat.card X := by
  rw [← card_conjClass_mul_card_centralizer z]
  congr 1
  refine Nat.card_congr (Equiv.subtypeEquivRight fun y => ?_)
  exact ⟨fun hy => (h.isConj_of_mem hZ hy hz), fun hy => hZ.isConj_mem hz hy⟩

theorem IsProductDisconnected.card_inter_mul_card_centralizer (hZ : IsInvariantInvolutionSet Z)
    (h : IsProductDisconnected Z M) {z : X} (hz : z ∈ Z) (hzM : z ∈ M) :
    Nat.card ↥(Z ∩ (M : Set X)) * Nat.card (centralizer ({z} : Set X)) = Nat.card M := by
  have hCM : centralizer ({z} : Set X) ≤ M := h.centralizer_le_of_mem hz hzM
  let z' : M := ⟨z, hzM⟩
  have h1 := card_conjClass_mul_card_centralizer z'
  have e1 : Nat.card {y : M // IsConj y z'} = Nat.card ↥(Z ∩ (M : Set X)) := by
    refine Nat.card_congr
      { toFun := fun y => ⟨(y : X), ?_, y.1.2⟩
        invFun := fun w => ⟨⟨w.1, w.2.2⟩, ?_⟩
        left_inv := fun y => rfl
        right_inv := fun w => rfl }
    · obtain ⟨c, hc⟩ := isConj_iff.mp y.2.symm
      have h2 := hZ.2 z hz (c : X)⁻¹
      have h3 : ((c * z' * c⁻¹ : M) : X) = (y : X) := congrArg Subtype.val hc
      simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h3
      rw [← h3]
      simpa using h2
    · obtain ⟨m, hmM, hm⟩ := h.exists_conj_mem hZ hz hzM w.2.1 w.2.2
      refine isConj_iff.mpr ⟨⟨m, hmM⟩, ?_⟩
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      show m * (w : X) * m⁻¹ = z
      rw [← hm]
      group
  have e2 : Nat.card (centralizer ({z'} : Set M)) = Nat.card (centralizer ({z} : Set X)) := by
    have : centralizer ({z'} : Set M) = (centralizer ({z} : Set X)).subgroupOf M := by
      ext x
      simp only [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_subgroupOf]
      constructor
      · intro hx
        exact congrArg Subtype.val hx
      · intro hx
        exact Subtype.ext hx
    rw [this]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCM).toEquiv
  rw [e1, e2] at h1
  exact h1

end Lemma34


section Lemma34a

variable {X : Type*} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}

theorem IsProductDisconnected.exists_mem_leftCoset (hZ : IsInvariantInvolutionSet Z)
    (h : IsProductDisconnected Z M) {z : X} (hz : z ∈ Z) (hzM : z ∈ M) {g : X} (hg : g ∉ M) :
    ∃ s ∈ Z, s⁻¹ * g ∈ centralizer ({z} : Set X) := by
  classical
  set C := centralizer ({z} : Set X) with hC
  have hCM : C ≤ M := h.centralizer_le_of_mem hz hzM
  let B := {s : X // s ∈ Z ∧ s ∉ M}
  let f : B × C → {g : X // g ∉ M} := fun p => ⟨(p.1 : X) * p.2, fun hmem => p.1.2.2 (by
    have := M.mul_mem hmem (M.inv_mem (hCM p.2.2))
    simpa using this)⟩
  have hinj : Function.Injective f := by
    rintro ⟨s, c⟩ ⟨s', c'⟩ hss'
    have h1 : (s : X) * c = (s' : X) * c' := congrArg Subtype.val hss'
    have hs'2 := hZ.mul_self_eq_one s'.2.1
    have e1 : (s' : X) * s * c = c' := by
      calc (s' : X) * s * c = (s' : X) * ((s : X) * c) := by rw [mul_assoc]
        _ = (s' : X) * ((s' : X) * c') := by rw [h1]
        _ = ((s' : X) * s') * c' := by rw [mul_assoc]
        _ = c' := by rw [hs'2, one_mul]
    have h2 : (s' : X) * s ∈ C := by
      have : (s' : X) * s = (c' : X) * (c : X)⁻¹ := by rw [← e1]; group
      rw [this]
      exact C.mul_mem c'.2 (C.inv_mem c.2)
    have hse : (s' : X) = s := h.eq_of_mul_mem_centralizer hZ hz hzM s'.2.1 s.2.1 s.2.2 h2
    have hs_eq : s' = s := Subtype.ext hse
    subst hs_eq
    have : (c : X) = c' := mul_left_cancel h1
    exact Prod.ext rfl (Subtype.ext this)
  have hcard : Nat.card {g : X // g ∉ M} ≤ Nat.card (B × C) := by
    have h1 : (Z ∩ (M : Set X)).ncard + (Z \ (M : Set X)).ncard = Z.ncard :=
      Set.ncard_inter_add_ncard_sdiff_eq_ncard Z (M : Set X) (Set.toFinite Z)
    have h2 : (M : Set X).ncard + (M : Set X)ᶜ.ncard = Nat.card X :=
      Set.ncard_add_ncard_compl (M : Set X) (Set.toFinite _)
    have hZ1 : Nat.card Z = Z.ncard := Nat.card_coe_set_eq Z
    have hZ2 : Nat.card ↥(Z ∩ (M : Set X)) = (Z ∩ (M : Set X)).ncard := Nat.card_coe_set_eq _
    have hM1 : Nat.card M = (M : Set X).ncard := Nat.card_coe_set_eq _
    have hB1 : Nat.card B = (Z \ (M : Set X)).ncard := Nat.card_coe_set_eq _
    have hA1 : Nat.card {g : X // g ∉ M} = (M : Set X)ᶜ.ncard := Nat.card_coe_set_eq _
    have hcardZ := h.card_mul_card_centralizer hZ hz
    have hcardZM := h.card_inter_mul_card_centralizer hZ hz hzM
    rw [hZ1] at hcardZ
    rw [hZ2, hM1] at hcardZM
    rw [Nat.card_prod, hB1, hA1]
    have e : Nat.card X = (M : Set X).ncard + (Z \ (M : Set X)).ncard * Nat.card C := by
      rw [← hcardZ, ← hcardZM, ← h1]; ring
    omega
  obtain ⟨⟨s, c⟩, hsc⟩ := (hinj.bijective_of_nat_card_le hcard).2 ⟨g, hg⟩
  refine ⟨s, s.2.1, ?_⟩
  have h1 : (s : X) * c = g := congrArg Subtype.val hsc
  rw [← h1, inv_mul_cancel_left]
  exact c.2

theorem IsProductDisconnected.existsUnique_mem_leftCoset (hZ : IsInvariantInvolutionSet Z)
    (h : IsProductDisconnected Z M) {z : X} (hz : z ∈ Z) (hzM : z ∈ M) {g : X} (hg : g ∉ M) :
    ∃! s : X, s ∈ Z ∧ s⁻¹ * g ∈ centralizer ({z} : Set X) := by
  obtain ⟨s, hs, hsC⟩ := h.exists_mem_leftCoset hZ hz hzM hg
  have hCM : centralizer ({z} : Set X) ≤ M := h.centralizer_le_of_mem hz hzM
  have hnot : ∀ t : X, t⁻¹ * g ∈ centralizer ({z} : Set X) → t ∉ M := by
    intro t ht htM
    apply hg
    have := M.mul_mem htM (hCM ht)
    simpa using this
  refine ⟨s, ⟨hs, hsC⟩, ?_⟩
  rintro t ⟨ht, htC⟩
  have hs2 := hZ.mul_self_eq_one hs
  have hsi : (s : X)⁻¹ = s := inv_eq_of_mul_eq_one_right hs2
  have hst : s * t ∈ centralizer ({z} : Set X) := by
    have h1 := (centralizer ({z} : Set X)).mul_mem hsC ((centralizer ({z} : Set X)).inv_mem htC)
    have h2 : s⁻¹ * g * (t⁻¹ * g)⁻¹ = s * t := by rw [hsi]; group
    rw [← h2]; exact h1
  exact (h.eq_of_mul_mem_centralizer hZ hz hzM hs ht (hnot t htC) hst).symm

theorem IsProductDisconnected.existsUnique_mem_rightCoset (hZ : IsInvariantInvolutionSet Z)
    (h : IsProductDisconnected Z M) {z : X} (hz : z ∈ Z) (hzM : z ∈ M) {g : X} (hg : g ∉ M) :
    ∃! s : X, s ∈ Z ∧ s * g⁻¹ ∈ centralizer ({z} : Set X) := by
  have hg' : g⁻¹ ∉ M := fun hmem => hg (M.inv_mem_iff.mp hmem)
  obtain ⟨s, ⟨hs, hsC⟩, huniq⟩ := h.existsUnique_mem_leftCoset hZ hz hzM hg'
  have hinv : ∀ {u : X}, u ∈ Z → u⁻¹ = u := fun {u} hu =>
    inv_eq_of_mul_eq_one_right (hZ.mul_self_eq_one hu)
  refine ⟨s, ⟨hs, by rwa [hinv hs] at hsC⟩, fun t ⟨ht, htC⟩ => huniq t ⟨ht, ?_⟩⟩
  rwa [hinv ht]

theorem IsProductDisconnected.card_leftCoset (hZ : IsInvariantInvolutionSet Z)
    (h : IsProductDisconnected Z M) {z : X} (hz : z ∈ Z) (hzM : z ∈ M) (g : X) :
    Nat.card {s : X // s ∈ Z ∧ g⁻¹ * s ∈ M} = Nat.card {s : X // s ∈ Z ∧ s ∈ M} := by
  by_cases hg : g ∈ M
  · refine Nat.card_congr (Equiv.subtypeEquivRight fun s => and_congr_right fun _ => ?_)
    constructor
    · intro hs; simpa using M.mul_mem hg hs
    · intro hs; exact M.mul_mem (M.inv_mem hg) hs
  set C := centralizer ({z} : Set X) with hC
  have hCM : C ≤ M := h.centralizer_le_of_mem hz hzM
  have hCpos : 0 < Nat.card C := Nat.card_pos
  let T := {s : X // s ∈ Z ∧ g⁻¹ * s ∈ M}
  let F : T × C → {x : X // g⁻¹ * x ∈ M} := fun p =>
    ⟨(p.1 : X) * p.2, by
      have := M.mul_mem p.1.2.2 (hCM p.2.2)
      simpa [mul_assoc] using this⟩
  have hnotM : ∀ x : X, g⁻¹ * x ∈ M → x ∉ M := fun x hx hxM => hg (by
    have := M.mul_mem hx (M.inv_mem hxM)
    simpa using M.inv_mem this)
  have hinj : Function.Injective F := by
    rintro ⟨s, c⟩ ⟨s', c'⟩ hss'
    have h1 : (s : X) * c = (s' : X) * c' := congrArg Subtype.val hss'
    have hs'2 := hZ.mul_self_eq_one s'.2.1
    have e1 : (s' : X) * s * c = c' := by
      calc (s' : X) * s * c = (s' : X) * ((s : X) * c) := by rw [mul_assoc]
        _ = (s' : X) * ((s' : X) * c') := by rw [h1]
        _ = ((s' : X) * s') * c' := by rw [mul_assoc]
        _ = c' := by rw [hs'2, one_mul]
    have h2 : (s' : X) * s ∈ C := by
      have : (s' : X) * s = (c' : X) * (c : X)⁻¹ := by rw [← e1]; group
      rw [this]
      exact C.mul_mem c'.2 (C.inv_mem c.2)
    have hse : (s' : X) = s := h.eq_of_mul_mem_centralizer hZ hz hzM s'.2.1 s.2.1
      (hnotM _ s.2.2) h2
    have hs_eq : s' = s := Subtype.ext hse
    subst hs_eq
    have : (c : X) = c' := mul_left_cancel h1
    exact Prod.ext rfl (Subtype.ext this)
  have hsurj : Function.Surjective F := by
    rintro ⟨x, hx⟩
    obtain ⟨s, hs, hsC⟩ := h.exists_mem_leftCoset hZ hz hzM (hnotM x hx)
    refine ⟨(⟨s, hs, ?_⟩, ⟨s⁻¹ * x, hsC⟩), ?_⟩
    · have := M.mul_mem hx (M.inv_mem (hCM hsC))
      have h3 : g⁻¹ * x * (s⁻¹ * x)⁻¹ = g⁻¹ * s := by group
      rwa [← h3]
    · apply Subtype.ext
      show s * (s⁻¹ * x) = x
      group
  have hcardF : Nat.card (T × C) = Nat.card {x : X // g⁻¹ * x ∈ M} :=
    Nat.card_congr (Equiv.ofBijective F ⟨hinj, hsurj⟩)
  have hcardM : Nat.card {x : X // g⁻¹ * x ∈ M} = Nat.card M :=
    Nat.card_congr
      { toFun := fun x => ⟨g⁻¹ * x, x.2⟩
        invFun := fun m => ⟨g * m, by simp⟩
        left_inv := fun x => by apply Subtype.ext; simp
        right_inv := fun m => by apply Subtype.ext; simp }
  rw [Nat.card_prod, hcardM] at hcardF
  have hZM := h.card_inter_mul_card_centralizer hZ hz hzM
  have hZM' : Nat.card ↥(Z ∩ (M : Set X)) = Nat.card {s : X // s ∈ Z ∧ s ∈ M} :=
    Nat.card_congr (Equiv.refl _)
  rw [hZM', ← hcardF] at hZM
  exact (Nat.eq_of_mul_eq_mul_right hCpos hZM).symm

theorem IsProductDisconnected.card_rightCoset (hZ : IsInvariantInvolutionSet Z)
    (h : IsProductDisconnected Z M) {z : X} (hz : z ∈ Z) (hzM : z ∈ M) (g : X) :
    Nat.card {s : X // s ∈ Z ∧ s * g⁻¹ ∈ M} = Nat.card {s : X // s ∈ Z ∧ s ∈ M} := by
  rw [← h.card_leftCoset hZ hz hzM g⁻¹]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun s => and_congr_right fun hs => ?_)
  have hsi : s⁻¹ = s := inv_eq_of_mul_eq_one_right (hZ.mul_self_eq_one hs)
  rw [← M.inv_mem_iff, mul_inv_rev, inv_inv, hsi]

theorem IsProductDisconnected.exists_mem_rightCoset (hZ : IsInvariantInvolutionSet Z)
    (h : IsProductDisconnected Z M) (g : X) : ∃ s ∈ Z, s * g⁻¹ ∈ M := by
  obtain ⟨z, hz, hzM⟩ := h.2.1
  have hpos : 0 < Nat.card {s : X // s ∈ Z ∧ s ∈ M} := by
    have : Nonempty {s : X // s ∈ Z ∧ s ∈ M} := ⟨⟨z, hz, hzM⟩⟩
    exact Nat.card_pos
  have h1 := h.card_leftCoset hZ hz hzM g⁻¹
  rw [← h1] at hpos
  obtain ⟨⟨s, hs, hsM⟩⟩ := Nat.card_pos_iff.mp hpos |>.1
  refine ⟨s, hs, ?_⟩
  have hs2 := hZ.mul_self_eq_one hs
  have hsi : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs2
  have := M.inv_mem hsM
  rwa [inv_inv ,mul_inv_rev, hsi] at this

end Lemma34a

end CFSG.GH74.Uniqueness
