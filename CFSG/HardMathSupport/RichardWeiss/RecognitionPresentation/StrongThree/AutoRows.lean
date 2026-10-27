module

public import CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree.Gls3Plus

public section

namespace CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree

open Subgroup

theorem ActsIrr.mono {X : Type*} [Group X] {N N' R : Subgroup X} (h : ActsIrr N R) (hN : N ≤ N') :
    ActsIrr N' R := fun W hWR hW => h W hWR (hN.trans hW)

theorem exists_cyclic_sylow_two_of_card_eq {X : Type*} [Group X] [Finite X] {Γ : Subgroup X}
    (h : Nat.card Γ = 18) :
    ∃ T : Subgroup X, T ≤ Γ ∧ IsPGroup 2 T ∧ ¬ 2 ∣ T.relIndex Γ ∧ IsCyclic ↥T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T₀⟩ : Nonempty (Sylow 2 ↥Γ) := inferInstance
  have hTΓ : (T₀ : Subgroup ↥Γ).map Γ.subtype ≤ Γ := Subgroup.map_subtype_le _
  have hsub : ((T₀ : Subgroup ↥Γ).map Γ.subtype).subgroupOf Γ = T₀ :=
    Subgroup.comap_map_eq_self_of_injective Γ.subtype_injective _
  have hcard : Nat.card T₀ = 2 := by
    rw [Sylow.card_eq_multiplicity, h]
    have : (18 : ℕ).factorization 2 = 1 := by
      have h18 : (18 : ℕ) = 2 ^ 1 * 9 := by norm_num
      rw [h18, Nat.factorization_mul (by norm_num) (by norm_num)]
      simp [Nat.Prime.factorization_self Nat.prime_two,
        Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 9)]
    rw [this]; norm_num
  refine ⟨(T₀ : Subgroup ↥Γ).map Γ.subtype, hTΓ, T₀.isPGroup'.map _, ?_, ?_⟩
  · show ¬ 2 ∣ (((T₀ : Subgroup ↥Γ).map Γ.subtype).subgroupOf Γ).index
    rw [hsub]; exact T₀.not_dvd_index
  · have hc : Nat.card ↥((T₀ : Subgroup ↥Γ).map Γ.subtype) = 2 :=
      (Nat.card_congr (Subgroup.equivMapOfInjective (T₀ : Subgroup ↥Γ) Γ.subtype
        Γ.subtype_injective).toEquiv).symm.trans hcard
    have : Fact (Nat.card ↥((T₀ : Subgroup ↥Γ).map Γ.subtype)).Prime :=
      ⟨by rw [hc]; exact Nat.prime_two⟩
    exact isCyclic_of_prime_card hc

theorem card_sup_of_normal_disjoint {X : Type*} [Group X] [Finite X] {Γ Q S : Subgroup X}
    (hΓ : Γ = Q ⊔ S) (hN : Γ ≤ Subgroup.normalizer (Q : Set X)) (hd : Q ⊓ S = ⊥) :
    Nat.card Γ = Nat.card Q * Nat.card S := by
  have hQΓ : Q ≤ Γ := hΓ ▸ le_sup_left
  have hSΓ : S ≤ Γ := hΓ ▸ le_sup_right
  have hQn : (Q.subgroupOf Γ).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hQΓ).mpr hN
  let f : ↥S →* (↥Γ ⧸ Q.subgroupOf Γ) :=
    (QuotientGroup.mk' (Q.subgroupOf Γ)).comp (Subgroup.inclusion hSΓ)
  have hf : Function.Surjective f := by
    intro x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    have hsup : Q.subgroupOf Γ ⊔ S.subgroupOf Γ = ⊤ := by
      rw [← Subgroup.subgroupOf_sup hQΓ hSΓ, ← hΓ, Subgroup.subgroupOf_self]
    have hg : g ∈ (S.subgroupOf Γ ⊔ Q.subgroupOf Γ : Subgroup ↥Γ) := by
      rw [sup_comm, hsup]; exact Subgroup.mem_top g
    have hg' : g ∈ ((S.subgroupOf Γ ⊔ Q.subgroupOf Γ : Subgroup ↥Γ) : Set ↥Γ) := hg
    rw [Subgroup.mul_normal] at hg'
    obtain ⟨s', hs', q', hq', rfl⟩ := hg'
    refine ⟨⟨(s' : X), hs'⟩, ?_⟩
    show QuotientGroup.mk (Subgroup.inclusion hSΓ ⟨(s' : X), hs'⟩) = QuotientGroup.mk (s' * q')
    rw [QuotientGroup.eq]
    have h1 : Subgroup.inclusion hSΓ ⟨(s' : X), hs'⟩ = s' := rfl
    rw [h1, inv_mul_cancel_left]
    exact hq'
  have hinj : Function.Injective f := by
    refine (injective_iff_map_eq_one f).mpr fun x hx => ?_
    have hxQ : (Subgroup.inclusion hSΓ x : ↥Γ) ∈ Q.subgroupOf Γ := (QuotientGroup.eq_one_iff _).mp hx
    have hmem : (x : X) ∈ Q ⊓ S := ⟨hxQ, x.2⟩
    rw [hd, Subgroup.mem_bot] at hmem
    exact Subtype.ext hmem
  have hcard1 : Nat.card S = Nat.card (↥Γ ⧸ Q.subgroupOf Γ) :=
    Nat.card_congr (Equiv.ofBijective f ⟨hinj, hf⟩)
  have hcard2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (Q.subgroupOf Γ)
  have hcard3 : Nat.card (Q.subgroupOf Γ) = Nat.card Q :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQΓ).toEquiv
  rw [hcard2, hcard3, hcard1, mul_comm]

theorem transitive_of_quasidihedral {X : Type*} [Group X] [Finite X] {Q S : Subgroup X}
    (hQc : Nat.card Q = 9) (hSN : S ≤ Subgroup.normalizer (Q : Set X))
    (hirr : ActsIrr S Q) (hC : S ⊓ Subgroup.centralizer (Q : Set X) = ⊥)
    {a b : X} (ha : a ∈ S) (hb : b ∈ S) (ho8 : orderOf a = 8) (hbab : b * a * b⁻¹ = a ^ 3)
    (hS : S = Subgroup.closure {a, b}) :
    ∀ x ∈ Q, ∀ y ∈ Q, x ≠ 1 → y ≠ 1 → ∃ s ∈ S, s * x * s⁻¹ = y := by
  classical
  set t : X := a ^ 4 with ht
  have ha8 : a ^ 8 = 1 := by rw [← ho8]; exact pow_orderOf_eq_one a
  have ht_ne : t ≠ 1 := by
    intro h
    have := orderOf_dvd_of_pow_eq_one h
    rw [ho8] at this
    omega
  have ht_S : t ∈ S := S.pow_mem ha 4
  have ht_nC : t ∉ Subgroup.centralizer (Q : Set X) := by
    intro h
    have : t ∈ S ⊓ Subgroup.centralizer (Q : Set X) := ⟨ht_S, h⟩
    rw [hC, Subgroup.mem_bot] at this
    exact ht_ne this
  have hbt : b * t * b⁻¹ = t := by
    have : b * a ^ 4 * b⁻¹ = (b * a * b⁻¹) ^ 4 := by
      rw [conj_pow]
    rw [ht, this, hbab, ← pow_mul]
    have : a ^ (3 * 4) = a ^ 4 * a ^ 8 := by rw [← pow_add]
    rw [this, ha8, mul_one]
  have hcent : ∀ s ∈ S, s * t = t * s := by
    intro s hs
    rw [hS] at hs
    induction hs using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with rfl | rfl
      · exact (Commute.pow_right (Commute.refl x) 4).eq
      · have := hbt
        calc x * t = (x * t * x⁻¹) * x := by group
          _ = t * x := by rw [this]
    | one => simp
    | mul x y _ _ hx hy => rw [mul_assoc, hy, ← mul_assoc, hx, mul_assoc]
    | inv x _ hx =>
      have : x⁻¹ * t = t * x⁻¹ := by
        calc x⁻¹ * t = x⁻¹ * (t * x) * x⁻¹ := by rw [mul_assoc, mul_inv_cancel_right]
          _ = x⁻¹ * (x * t) * x⁻¹ := by rw [hx]
          _ = t * x⁻¹ := by group
      exact this
  set W : Subgroup X := Q ⊓ Subgroup.centralizer ({t} : Set X) with hW
  have hWconj : ∀ s ∈ S, ∀ w ∈ W, s * w * s⁻¹ ∈ W := by
    intro s hs w hw
    refine ⟨(Subgroup.mem_normalizer_iff.mp (hSN hs) w).mp hw.1, ?_⟩
    show s * w * s⁻¹ ∈ Subgroup.centralizer ({t} : Set X)
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hwt : w * t = t * w := Subgroup.mem_centralizer_singleton_iff.mp hw.2
    calc s * w * s⁻¹ * t = s * w * (s⁻¹ * t) := by rw [mul_assoc]
      _ = s * w * (t * s⁻¹) := by
        congr 1
        have := hcent s⁻¹ (S.inv_mem hs)
        exact this
      _ = s * (w * t) * s⁻¹ := by group
      _ = s * (t * w) * s⁻¹ := by rw [hwt]
      _ = t * (s * w * s⁻¹) := by
        have := hcent s hs
        calc s * (t * w) * s⁻¹ = (s * t) * w * s⁻¹ := by group
          _ = (t * s) * w * s⁻¹ := by rw [this]
          _ = t * (s * w * s⁻¹) := by group
  have hWS : S ≤ Subgroup.normalizer (W : Set X) := by
    intro s hs
    rw [Subgroup.mem_normalizer_iff]
    intro w
    refine ⟨fun hw => hWconj s hs w hw, fun hw => ?_⟩
    have := hWconj s⁻¹ (S.inv_mem hs) _ hw
    have e : s⁻¹ * (s * w * s⁻¹) * s⁻¹⁻¹ = w := by group
    rwa [e] at this
  have hW0 : W = ⊥ := by
    rcases hirr W inf_le_left hWS with h | h
    · exact h
    · exfalso
      apply ht_nC
      rw [Subgroup.mem_centralizer_iff]
      intro q hq
      have : q ∈ W := h ▸ hq
      exact Subgroup.mem_centralizer_singleton_iff.mp this.2
  have hfix : ∀ x ∈ Q, t * x = x * t → x = 1 := by
    intro x hx h
    have : x ∈ W := ⟨hx, Subgroup.mem_centralizer_singleton_iff.mpr h.symm⟩
    rw [hW0, Subgroup.mem_bot] at this
    exact this
  intro x hxQ y hyQ hx1 hy1
  let f : ℕ → X := fun i => a ^ i * x * (a ^ i)⁻¹
  have hfQ : ∀ i, f i ∈ Q := fun i =>
    (Subgroup.mem_normalizer_iff.mp (hSN (S.pow_mem ha i)) x).mp hxQ
  have hf1 : ∀ i, f i ≠ 1 := fun i h => hx1 (by
    have : a ^ i * x * (a ^ i)⁻¹ = 1 := h
    simpa using this)
  have hinj : ∀ i j : ℕ, i < 8 → j < 8 → i < j → f i ≠ f j := by
    intro i j hi hj hij heq
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hij
    have hk : a ^ (k + 1) * x = x * a ^ (k + 1) := by
      have h1 : a ^ i * x * (a ^ i)⁻¹ = a ^ (i + k + 1) * x * (a ^ (i + k + 1))⁻¹ := heq
      have e : a ^ (i + k + 1) = a ^ i * a ^ (k + 1) := by rw [← pow_add]; ring_nf
      rw [e] at h1
      have h2 : x = a ^ (k + 1) * x * (a ^ (k + 1))⁻¹ := by
        have := congrArg (fun z => (a ^ i)⁻¹ * z * a ^ i) h1
        simpa [mul_assoc] using this
      calc a ^ (k + 1) * x = (a ^ (k + 1) * x * (a ^ (k + 1))⁻¹) * a ^ (k + 1) := by group
        _ = x * a ^ (k + 1) := by rw [← h2]
    have hk8 : k + 1 < 8 := by omega
    obtain ⟨m, hm⟩ : ∃ m : ℕ, ((k + 1) * m) % 8 = 4 := by
      have : ∀ k' : Fin 8, k' ≠ 0 → ∃ m : Fin 8, (k' * m : ℕ) % 8 = 4 := by decide
      obtain ⟨m, hm⟩ := this ⟨k + 1, hk8⟩ (by simp [Fin.ext_iff])
      exact ⟨m, hm⟩
    have hcomm : Commute ((a ^ (k + 1)) ^ m) x := (Commute.pow_left hk m)
    have : (a ^ (k + 1)) ^ m = t := by
      rw [← pow_mul, ← pow_mod_orderOf, ho8, hm]
    rw [this] at hcomm
    exact hx1 (hfix x hxQ hcomm.eq)
  let g : Fin 8 → {z : ↥Q // z ≠ 1} := fun i => ⟨⟨f i, hfQ i⟩, fun h => hf1 i (congrArg Subtype.val h)⟩
  have hgi : Function.Injective g := by
    intro i j hij
    have hfij : f i = f j := congrArg (fun z => (z.1 : X)) hij
    by_contra hne
    rcases lt_or_gt_of_ne (fun h : (i : ℕ) = j => hne (Fin.ext h)) with h | h
    · exact hinj i j i.2 j.2 h hfij
    · exact hinj j i j.2 i.2 h hfij.symm
  have hcardB : Nat.card {z : ↥Q // z ≠ 1} ≤ Nat.card (Fin 8) := by
    have : Fintype ↥Q := Fintype.ofFinite _
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_subtype_compl,
      Fintype.card_subtype_eq, ← Nat.card_eq_fintype_card, hQc]
    simp
  have hbij : Function.Bijective g := hgi.bijective_of_nat_card_le hcardB
  obtain ⟨i, hi⟩ := hbij.2 ⟨⟨y, hyQ⟩, fun h => hy1 (congrArg Subtype.val h)⟩
  refine ⟨a ^ (i : ℕ), S.pow_mem ha i, ?_⟩
  have := congrArg (fun z => (z.1 : X)) hi
  simpa [f] using this

end CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree
