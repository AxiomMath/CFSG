module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingFixedSupport
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerSemidihedralTwoComponents

public section

namespace CFSG.ComponentClassification.HSFLit.HS7

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer

theorem nat_card_alternating_seven : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  decide

section Perm

variable {n : ℕ}

theorem eq_top_of_alternating_le {K : Subgroup (Equiv.Perm (Fin n))}
    (hK : alternatingGroup (Fin n) ≤ K) {σ : Equiv.Perm (Fin n)} (hσK : σ ∈ K)
    (hσ : σ ∉ alternatingGroup (Fin n)) : K = ⊤ := by
  rw [eq_top_iff]
  intro τ _
  by_cases hτ : τ ∈ alternatingGroup (Fin n)
  · exact hK hτ
  · rw [Equiv.Perm.mem_alternatingGroup] at hσ hτ
    have hs : Equiv.Perm.sign σ = -1 := (Int.units_eq_one_or _).resolve_left hσ
    have ht : Equiv.Perm.sign τ = -1 := (Int.units_eq_one_or _).resolve_left hτ
    have h1 : τ * σ⁻¹ ∈ alternatingGroup (Fin n) := by
      rw [Equiv.Perm.mem_alternatingGroup, map_mul, map_inv, hs, ht]
      decide
    have h2 := mul_mem (hK h1) hσK
    rwa [inv_mul_cancel_right] at h2

theorem normalizer_zpowers_eq_centralizer {X : Type*} [Group X] {σ : X} (hσ : orderOf σ = 2) :
    normalizer ((zpowers σ : Subgroup X) : Set X) = centralizer ({σ} : Set X) := by
  ext g
  rw [mem_centralizer_singleton_iff, mem_normalizer_iff]
  constructor
  · intro hg
    have h1 : g * σ * g⁻¹ ∈ zpowers σ := (hg σ).mp (mem_zpowers σ)
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp h1
    rw [← zpow_mod_orderOf, hσ] at hk
    push_cast at hk
    rcases Int.emod_two_eq k with h0 | h0
    · rw [h0, zpow_zero] at hk
      have h2 : σ = 1 := by
        calc σ = g⁻¹ * (g * σ * g⁻¹) * g := by group
          _ = 1 := by rw [← hk]; group
      rw [h2, orderOf_one] at hσ
      exact absurd hσ (by decide)
    · rw [h0, zpow_one] at hk
      calc g * σ = (g * σ * g⁻¹) * g := by group
        _ = σ * g := by rw [← hk]
  · intro hg h
    have hcomm : g * σ * g⁻¹ = σ := by rw [hg, mul_inv_cancel_right]
    constructor
    · intro hh
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hh
      refine ⟨k, ?_⟩
      rw [← conj_zpow, hcomm]
    · intro hh
      obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hh
      refine ⟨k, ?_⟩
      have h1 : g * σ ^ k * g⁻¹ = σ ^ k := by rw [← conj_zpow, hcomm]
      calc σ ^ k = g⁻¹ * (g * σ ^ k * g⁻¹) * g := by group
        _ = g⁻¹ * σ ^ k * g := by rw [h1]
        _ = g⁻¹ * (g * h * g⁻¹) * g := by rw [hk]
        _ = h := by group

theorem mem_fixedPoints_zpowers {Ω : Type*} {σ : Equiv.Perm Ω} {x : Ω} :
    x ∈ MulAction.fixedPoints (zpowers σ) Ω ↔ σ x = x := by
  rw [MulAction.mem_fixedPoints]
  constructor
  · intro h
    exact h ⟨σ, mem_zpowers σ⟩
  · rintro h ⟨g, hg⟩
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hg
    show (σ ^ k) x = x
    exact (Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self h k)

theorem card_fixedPoints_add_card_support (σ : Equiv.Perm (Fin n)) :
    Nat.card (MulAction.fixedPoints (zpowers σ) (Fin n)) + σ.support.card = n := by
  classical
  have h1 : Nat.card (MulAction.fixedPoints (zpowers σ) (Fin n)) =
      (Finset.univ.filter fun x => σ x = x).card := by
    rw [← Nat.card_eq_finsetCard]
    apply Nat.card_congr
    exact Equiv.subtypeEquivRight fun x => by
      rw [mem_fixedPoints_zpowers]
      simp
  have h2 : σ.support = Finset.univ.filter fun x => σ x ≠ x := by
    ext x
    simp [Equiv.Perm.mem_support]
  rw [h1, h2]
  have h3 := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin n))) (fun x => σ x = x)
  rw [Finset.card_univ, Fintype.card_fin] at h3
  exact h3

theorem klein_facts {Ω : Type*} [DecidableEq Ω] {a b c d : Ω} (hab : a ≠ b) (hac : a ≠ c)
    (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    let x := Equiv.swap a b * Equiv.swap c d
    let y := Equiv.swap a c * Equiv.swap b d
    x ≠ 1 ∧ y ≠ 1 ∧ x ≠ y ∧ x * x = 1 ∧ y * y = 1 ∧ x * y = y * x := by
  intro x y
  have sw := fun {p q z : Ω} (h1 : z ≠ p) (h2 : z ≠ q) => Equiv.swap_apply_of_ne_of_ne h1 h2
  have xa : x a = b := by
    simp only [x, Equiv.Perm.mul_apply, sw hac had, Equiv.swap_apply_left]
  have xb : x b = a := by
    simp only [x, Equiv.Perm.mul_apply, sw hbc hbd, Equiv.swap_apply_right]
  have xc : x c = d := by
    simp only [x, Equiv.Perm.mul_apply, Equiv.swap_apply_left, sw had.symm hbd.symm]
  have xd : x d = c := by
    simp only [x, Equiv.Perm.mul_apply, Equiv.swap_apply_right, sw hac.symm hbc.symm]
  have ya : y a = c := by
    simp only [y, Equiv.Perm.mul_apply, sw hab had, Equiv.swap_apply_left]
  have yb : y b = d := by
    simp only [y, Equiv.Perm.mul_apply, Equiv.swap_apply_left, sw had.symm hcd.symm]
  have yc : y c = a := by
    simp only [y, Equiv.Perm.mul_apply, sw hbc.symm hcd, Equiv.swap_apply_right]
  have yd : y d = b := by
    simp only [y, Equiv.Perm.mul_apply, Equiv.swap_apply_right, sw hab.symm hbc]
  have xz : ∀ z, z ≠ a → z ≠ b → z ≠ c → z ≠ d → x z = z := by
    intro z h1 h2 h3 h4
    simp only [x, Equiv.Perm.mul_apply, sw h3 h4, sw h1 h2]
  have yz : ∀ z, z ≠ a → z ≠ b → z ≠ c → z ≠ d → y z = z := by
    intro z h1 h2 h3 h4
    simp only [y, Equiv.Perm.mul_apply, sw h2 h4, sw h1 h3]
  have key : ∀ f g : Equiv.Perm Ω, f a = g a → f b = g b → f c = g c → f d = g d →
      (∀ z, z ≠ a → z ≠ b → z ≠ c → z ≠ d → f z = g z) → f = g := by
    intro f g ha hb hc hd hz
    ext z
    by_cases h1 : z = a
    · rw [h1, ha]
    by_cases h2 : z = b
    · rw [h2, hb]
    by_cases h3 : z = c
    · rw [h3, hc]
    by_cases h4 : z = d
    · rw [h4, hd]
    exact hz z h1 h2 h3 h4
  refine ⟨fun h => hab ?_, fun h => hac ?_, fun h => hbc ?_, ?_, ?_, ?_⟩
  · have := congrArg (fun p : Equiv.Perm Ω => p a) h
    simp only [Equiv.Perm.one_apply, xa] at this
    exact this.symm
  · have := congrArg (fun p : Equiv.Perm Ω => p a) h
    simp only [Equiv.Perm.one_apply, ya] at this
    exact this.symm
  · have := congrArg (fun p : Equiv.Perm Ω => p a) h
    simp only [xa, ya] at this
    exact this
  · refine key _ _ ?_ ?_ ?_ ?_ ?_ <;> simp only [Equiv.Perm.mul_apply, Equiv.Perm.one_apply]
    · rw [xa, xb]
    · rw [xb, xa]
    · rw [xc, xd]
    · rw [xd, xc]
    · intro z h1 h2 h3 h4
      rw [xz z h1 h2 h3 h4, xz z h1 h2 h3 h4]
  · refine key _ _ ?_ ?_ ?_ ?_ ?_ <;> simp only [Equiv.Perm.mul_apply, Equiv.Perm.one_apply]
    · rw [ya, yc]
    · rw [yb, yd]
    · rw [yc, ya]
    · rw [yd, yb]
    · intro z h1 h2 h3 h4
      rw [yz z h1 h2 h3 h4, yz z h1 h2 h3 h4]
  · refine key _ _ ?_ ?_ ?_ ?_ ?_ <;> simp only [Equiv.Perm.mul_apply]
    · rw [ya, xc, xa, yb]
    · rw [yb, xd, xb, ya]
    · rw [yc, xa, xc, yd]
    · rw [yd, xb, xd, yc]
    · intro z h1 h2 h3 h4
      rw [yz z h1 h2 h3 h4, xz z h1 h2 h3 h4, yz z h1 h2 h3 h4]

end Perm

theorem false_of_two_commuting_involutions {Y : Type*} [Group Y] [Finite Y]
    (hcyc : ∀ R : Sylow 2 Y, IsCyclic (R : Subgroup Y)) {x y : Y} (hx1 : x ≠ 1) (hy1 : y ≠ 1)
    (hxy : x ≠ y) (hx : x * x = 1) (hy : y * y = 1) (hc : x * y = y * x) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hxo : orderOf x = 2 := orderOf_eq_prime (by rw [pow_two]; exact hx) hx1
  have hyo : orderOf y = 2 := orderOf_eq_prime (by rw [pow_two]; exact hy) hy1
  have hx2 : IsPGroup 2 (zpowers x) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, hxo, pow_one])
  have hy2 : IsPGroup 2 (zpowers y) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, hyo, pow_one])
  have hN : zpowers x ≤ normalizer ((zpowers y : Subgroup Y) : Set Y) := by
    rw [zpowers_le, mem_normalizer_iff]
    intro h
    have hcomm : ∀ k : ℤ, x * y ^ k * x⁻¹ = y ^ k := fun k => by
      rw [(Commute.zpow_right hc k).eq, mul_inv_cancel_right]
    constructor
    · intro hh
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hh
      rw [hcomm k]
      exact hh
    · intro hh
      obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hh
      have h1 : h = x⁻¹ * (x * h * x⁻¹) * x := by group
      have h2 : x⁻¹ * y ^ k * x = y ^ k := by
        calc x⁻¹ * y ^ k * x = x⁻¹ * (x * y ^ k * x⁻¹) * x := by rw [hcomm k]
          _ = y ^ k := by group
      rw [h1, ← hk, h2]
      exact zpow_mem (mem_zpowers y) k
  have hP := hx2.to_sup_of_normal_right' hy2 hN
  obtain ⟨R, hR⟩ := hP.exists_le_sylow
  have : IsCyclic (R : Subgroup Y) := hcyc R
  have hxR : x ∈ (R : Subgroup Y) := hR (mem_sup_left (mem_zpowers x))
  have hyR : y ∈ (R : Subgroup Y) := hR (mem_sup_right (mem_zpowers y))
  have : Fintype (R : Subgroup Y) := Fintype.ofFinite _
  have hle := IsCyclic.card_pow_eq_one_le (α := (R : Subgroup Y)) (n := 2) (by norm_num)
  have h3 : ({1, ⟨x, hxR⟩, ⟨y, hyR⟩} : Finset (R : Subgroup Y)) ⊆
      Finset.univ.filter fun a => a ^ 2 = 1 := by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases ha with rfl | rfl | rfl
    · exact one_pow 2
    · exact Subtype.ext (by simp [pow_two, hx])
    · exact Subtype.ext (by simp [pow_two, hy])
  have h4 := Finset.card_le_card h3
  have h5 : ({1, ⟨x, hxR⟩, ⟨y, hyR⟩} : Finset (R : Subgroup Y)).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_pair]
    · exact fun h => hxy (congrArg Subtype.val h)
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨fun h => hx1 (congrArg Subtype.val h).symm,
        fun h => hy1 (congrArg Subtype.val h).symm⟩
  omega

theorem mem_coreActionKernel_of_commute {G : Type} [Group G] {L : Subgroup G} {g : G}
    (hg : ∀ l ∈ L, l * g = g * l) : g ∈ coreActionKernel L := by
  refine mem_coreActionKernel.mpr ⟨?_, fun j hj => ?_⟩
  · rw [mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      have h1 : g * h * g⁻¹ = h := by
        calc g * h * g⁻¹ = (h * g) * g⁻¹ := by rw [hg h hh]
          _ = h := by group
      rw [h1]
      exact hh
    · intro hh
      have hc := hg _ hh
      have h1 : g * h = g * (g * h * g⁻¹) := by
        calc g * h = (g * h * g⁻¹) * g := by group
          _ = g * (g * h * g⁻¹) := hc
      rw [mul_left_cancel h1]
      exact hh
  · have hjg : j * g = g * j := hg j hj
    have h1 : j⁻¹ * g⁻¹ * j * g = 1 := by
      calc j⁻¹ * g⁻¹ * j * g = j⁻¹ * g⁻¹ * (j * g) := by group
        _ = j⁻¹ * g⁻¹ * (g * j) := by rw [hjg]
        _ = 1 := by group
    rw [h1]
    exact one_mem _

theorem false_of_support_ge_four {G : Type} [Group G] [Finite G] {n : ℕ} {L : Subgroup G}
    (hcyc : ∀ R : Sylow 2 ↥(coreActionKernel L), IsCyclic (R : Subgroup ↥(coreActionKernel L)))
    (e' : G ≃* Equiv.Perm (Fin n)) {σ : Equiv.Perm (Fin n)}
    (hL'N : L.map e'.toMonoidHom ≤
      normalizer ((zpowers σ : Subgroup (Equiv.Perm (Fin n))) : Set (Equiv.Perm (Fin n))))
    (hL'pN : IsPComponent 2 ((L.map e'.toMonoidHom).subgroupOf
      (normalizer ((zpowers σ : Subgroup (Equiv.Perm (Fin n))) : Set (Equiv.Perm (Fin n))))))
    (hP2 : IsPGroup 2 (zpowers σ)) (h4 : 4 ≤ σ.support.card) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, ha⟩ : σ.support.Nonempty := Finset.card_pos.mp (by omega)
  have h3 : 2 < (σ.support.erase a).card := by rw [Finset.card_erase_of_mem ha]; omega
  obtain ⟨b, c, d, hb, hc, hd, hbc, hbd, hcd⟩ := Finset.two_lt_card_iff.mp h3
  rw [Finset.mem_erase] at hb hc hd
  have hfix : ∀ l ∈ L, ∀ z, σ z ≠ z → e' l z = z := by
    intro l hl z hz
    have hmem : (⟨e' l, hL'N ⟨l, hl, rfl⟩⟩ : ↥(normalizer
        ((zpowers σ : Subgroup (Equiv.Perm (Fin n))) : Set (Equiv.Perm (Fin n))))) ∈
        (L.map e'.toMonoidHom).subgroupOf (normalizer
          ((zpowers σ : Subgroup (Equiv.Perm (Fin n))) : Set (Equiv.Perm (Fin n)))) :=
      mem_subgroupOf.mpr ⟨l, hl, rfl⟩
    exact CatalogueBAlternating.normalizer_pComponent_fixedSupport 2 _ hP2 _ hL'pN ⟨_, hmem⟩ z
      (fun h => hz (mem_fixedPoints_zpowers.mp h))
  have hcomm : ∀ x : Equiv.Perm (Fin n), (∀ z, σ z = z → x z = z) →
      ∀ l ∈ L, l * e'.symm x = e'.symm x * l := by
    intro x hx l hl
    have hdis : Equiv.Perm.Disjoint x (e' l) := by
      intro z
      by_cases hz : σ z = z
      · exact Or.inl (hx z hz)
      · exact Or.inr (hfix l hl z hz)
    have h1 : x * e' l = e' l * x := hdis.commute
    apply e'.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply, h1]
  have hne : ∀ w ∈ σ.support, ∀ z, σ z = z → z ≠ w := fun w hw z hz h =>
    (Equiv.Perm.mem_support.mp hw) (h ▸ hz)
  have hxz : ∀ z, σ z = z → (Equiv.swap a b * Equiv.swap c d) z = z := by
    intro z hz
    rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne (hne c hc.2 z hz) (hne d hd.2 z hz),
      Equiv.swap_apply_of_ne_of_ne (hne a ha z hz) (hne b hb.2 z hz)]
  have hyz : ∀ z, σ z = z → (Equiv.swap a c * Equiv.swap b d) z = z := by
    intro z hz
    rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne (hne b hb.2 z hz) (hne d hd.2 z hz),
      Equiv.swap_apply_of_ne_of_ne (hne a ha z hz) (hne c hc.2 z hz)]
  obtain ⟨hx1, hy1, hxy, hxx, hyy, hxyc⟩ :=
    klein_facts (Ne.symm hb.1) (Ne.symm hc.1) (Ne.symm hd.1) hbc hbd hcd
  let x' : ↥(coreActionKernel L) :=
    ⟨e'.symm (Equiv.swap a b * Equiv.swap c d), mem_coreActionKernel_of_commute (hcomm _ hxz)⟩
  let y' : ↥(coreActionKernel L) :=
    ⟨e'.symm (Equiv.swap a c * Equiv.swap b d), mem_coreActionKernel_of_commute (hcomm _ hyz)⟩
  refine false_of_two_commuting_involutions hcyc (x := x') (y := y') ?_ ?_ ?_ ?_ ?_ ?_
  · intro h
    apply hx1
    have h1 := congrArg (fun g : ↥(coreActionKernel L) => e' (g : G)) h
    simpa [x'] using h1
  · intro h
    apply hy1
    have h1 := congrArg (fun g : ↥(coreActionKernel L) => e' (g : G)) h
    simpa [y'] using h1
  · intro h
    apply hxy
    have h1 := congrArg (fun g : ↥(coreActionKernel L) => e' (g : G)) h
    simpa [x', y'] using h1
  · apply Subtype.ext
    show e'.symm _ * e'.symm _ = 1
    rw [← map_mul, hxx, map_one]
  · apply Subtype.ext
    show e'.symm _ * e'.symm _ = 1
    rw [← map_mul, hyy, map_one]
  · apply Subtype.ext
    show e'.symm _ * e'.symm _ = e'.symm _ * e'.symm _
    rw [← map_mul, ← map_mul, hxyc]

end CFSG.ComponentClassification.HSFLit.HS7
