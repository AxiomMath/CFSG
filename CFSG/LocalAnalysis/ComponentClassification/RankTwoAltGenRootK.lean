module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltGenY

public section

namespace CFSG.ComponentClassification.RankTwoAlt

open Equiv Equiv.Perm Subgroup CFSG.Open CFSG.ABGLocalTools
  CFSG.ComponentClassification.AschbacherTightEmbedding CFSG.ComponentClassification.AS76b
  CFSG.ComponentClassification.RankTwoStandard CFSG.ComponentClassification.RankTwoClassical
  CFSG.Quasithin.SteinbergCB

section Perm

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem apply_mem_support_of_commute {σ τ : Perm α} (h : σ * τ = τ * σ) {x : α}
    (hx : x ∈ τ.support) : σ x ∈ τ.support := by
  rw [mem_support] at hx ⊢
  intro h'
  apply hx
  apply σ.injective
  rw [← Perm.mul_apply, h, Perm.mul_apply, h']

theorem five_le_card_support_of_orderOf {σ : Perm α} (h : orderOf σ = 5) :
    5 ≤ σ.support.card := by
  have h1 : σ ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at h
    omega
  obtain ⟨k, hk⟩ : ∃ k, k ∈ σ.cycleType := by
    by_contra hall
    push Not at hall
    exact h1 (cycleType_eq_zero.mp (Multiset.eq_zero_of_forall_notMem hall))
  have hdvd := dvd_of_mem_cycleType hk
  rw [h] at hdvd
  have h2 := two_le_of_mem_cycleType hk
  have hk5 : k = 5 := by
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 5)).mp hdvd with h | h <;> omega
  rw [← sum_cycleType]
  calc 5 = k := hk5.symm
    _ ≤ σ.cycleType.sum := Multiset.le_sum_of_mem hk

theorem exists_four_ne {m : ℕ} (hm : 5 ≤ m) (i : Fin m) :
    ∃ a b c d : Fin m, i ≠ a ∧ i ≠ b ∧ i ≠ c ∧ i ≠ d ∧ a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧
      c ≠ d := by
  let f : Fin 4 → Fin m := fun k =>
    ⟨if (k : ℕ) < i then (k : ℕ) else (k : ℕ) + 1, by have := k.2; split_ifs <;> omega⟩
  have hf : ∀ k : Fin 4, ((f k : Fin m) : ℕ) = if (k : ℕ) < i then (k : ℕ) else (k : ℕ) + 1 :=
    fun _ => rfl
  have hne : ∀ k : Fin 4, i ≠ f k := by
    intro k h
    have h1 := congrArg Fin.val h
    rw [hf] at h1
    split_ifs at h1 <;> omega
  have hinj : ∀ k l : Fin 4, k ≠ l → f k ≠ f l := by
    intro k l hkl h
    have h1 := congrArg Fin.val h
    rw [hf, hf] at h1
    apply hkl
    apply Fin.ext
    split_ifs at h1 <;> omega
  exact ⟨f 0, f 1, f 2, f 3, hne 0, hne 1, hne 2, hne 3, hinj 0 1 (by decide),
    hinj 0 2 (by decide), hinj 0 3 (by decide), hinj 1 2 (by decide), hinj 1 3 (by decide),
    hinj 2 3 (by decide)⟩

theorem fix_of_commute_viaEmbeddingHom {m N : ℕ} (hm : 5 ≤ m) (ι : Fin m ↪ Fin N)
    {σ : Perm (Fin N)}
    (hσ : ∀ γ ∈ alternatingGroup (Fin m), σ * viaEmbeddingHom ι γ = viaEmbeddingHom ι γ * σ)
    (i : Fin m) : σ (ι i) = ι i := by
  have key : ∀ a b : Fin m, i ≠ a → i ≠ b → a ≠ b →
      σ (ι i) = ι i ∨ σ (ι i) = ι a ∨ σ (ι i) = ι b := by
    intro a b hia hib hab
    have hmem : swap i a * swap a b ∈ alternatingGroup (Fin m) := by
      rw [mem_alternatingGroup, Perm.sign_mul, sign_swap hia, sign_swap hab]
      rfl
    have hc := hσ _ hmem
    rw [map_mul, viaEmbeddingHom_swap, viaEmbeddingHom_swap] at hc
    have hnd : [ι i, ι a, ι b].Nodup := by
      simp [ι.injective.eq_iff, hia, hib, hab]
    have h1 := apply_mem_support_of_commute hc (x := ι i)
      (by rw [support_swap_mul_swap hnd]; simp)
    rw [support_swap_mul_swap hnd] at h1
    simpa using h1
  obtain ⟨a, b, c, d, hia, hib, hic, hid, hab, hac, had, hbc, hbd, hcd⟩ := exists_four_ne hm i
  have h1 := key a b hia hib hab
  have h2 := key c d hic hid hcd
  rcases h1 with h1 | h1 | h1
  · exact h1
  · rcases h2 with h2 | h2 | h2
    · exact h2
    · exact absurd (ι.injective (h1.symm.trans h2)) hac
    · exact absurd (ι.injective (h1.symm.trans h2)) had
  · rcases h2 with h2 | h2 | h2
    · exact h2
    · exact absurd (ι.injective (h1.symm.trans h2)) hbc
    · exact absurd (ι.injective (h1.symm.trans h2)) hbd

end Perm

namespace AltGenCore

variable {G : Type} [Group G] [Finite G] {A R T : Subgroup G} {g : G} {n : ℕ}
  {Φ : alternatingGroup (Fin (n + 4)) →* G} (s : AltGenCore A R T g n Φ)
include s

theorem fix_of_mem_centralizer {π : alternatingGroup (Fin (n + 4))}
    (hπ : Φ π ∈ centralizer (A : Set G)) (i : Fin n) :
    (π : Perm (Fin (n + 4))) (Fin.castLEEmb (by omega : n ≤ n + 4) i) =
      Fin.castLEEmb (by omega : n ≤ n + 4) i := by
  refine fix_of_commute_viaEmbeddingHom s.five_le _ (fun γ hγ => ?_) i
  have hc : Φ π * Φ (liftNat n ⟨γ, hγ⟩) = Φ (liftNat n ⟨γ, hγ⟩) * Φ π :=
    (mem_centralizer_iff.mp hπ _ (s.liftNat_mem ⟨γ, hγ⟩)).symm
  rw [← map_mul, ← map_mul] at hc
  have h1 := congrArg Subtype.val (s.injective hc)
  rw [Subgroup.coe_mul, Subgroup.coe_mul, coe_liftNat] at h1
  exact h1

theorem card_support_le_four_of_mem_centralizer {π : alternatingGroup (Fin (n + 4))}
    (hπ : Φ π ∈ centralizer (A : Set G)) : (π : Perm (Fin (n + 4))).support.card ≤ 4 := by
  have hsub : (π : Perm (Fin (n + 4))).support ⊆ Finset.univ.map (Fin.natAddEmb n) := by
    intro x hx
    rw [Finset.mem_map]
    by_cases hxn : (x : ℕ) < n
    · exfalso
      have h1 := s.fix_of_mem_centralizer hπ ⟨x, hxn⟩
      rw [mem_support] at hx
      apply hx
      have h2 : (Fin.castLEEmb (by omega : n ≤ n + 4) ⟨x, hxn⟩ : Fin (n + 4)) = x :=
        Fin.ext (by simp)
      rw [h2] at h1
      exact h1
    · refine ⟨⟨(x : ℕ) - n, by omega⟩, Finset.mem_univ _, Fin.ext ?_⟩
      simp only [Fin.natAddEmb_apply, Fin.val_natAdd]
      omega
  calc (π : Perm (Fin (n + 4))).support.card ≤ (Finset.univ.map (Fin.natAddEmb n)).card :=
        Finset.card_le_card hsub
    _ = 4 := by rw [Finset.card_map, Finset.card_univ, Fintype.card_fin]

theorem inf_centralizer_eq_bot : A ⊓ centralizer (A : Set G) = ⊥ := by
  have hn := s.five_le
  rw [eq_bot_iff]
  rintro a ⟨haA, haK⟩
  rw [mem_bot]
  obtain ⟨z, rfl⟩ := s.exists_liftNat_eq haA
  have hz : z ∈ center (alternatingGroup (Fin n)) := by
    rw [mem_center_iff]
    intro w
    have h1 : Φ (liftNat n (w * z)) = Φ (liftNat n (z * w)) := by
      rw [map_mul, map_mul, map_mul, map_mul]
      exact mem_centralizer_iff.mp haK _ (s.liftNat_mem w)
    exact liftNat_injective (s.injective h1)
  have h4 : 4 ≤ Nat.card (Fin n) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_fin]
    omega
  rw [alternatingGroup.center_eq_bot h4, mem_bot] at hz
  rw [hz, map_one, map_one]

theorem not_simple_le_centralizer {S : Subgroup G}
    (hSK : S ≤ centralizer (A : Set G)) (hS : IsSimpleGroup S) (h2 : Even (Nat.card S))
    (h5 : 5 ∣ Nat.card S) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' 2 (even_iff_two_dvd.mp h2)
  have htt : (t : G) * t = 1 := by
    have h1 := pow_orderOf_eq_one t
    rw [ht, sq] at h1
    exact congrArg Subtype.val h1
  have htY : (t : G) ∈ Φ.range :=
    s.mem_of_mem_sup_of_mul_self (s.centralizer_le (hSK t.2)) htt
  have hSY : S ≤ Φ.range := by
    have hN : (Φ.range.subgroupOf S).Normal := ⟨fun a ha b => by
      rw [mem_subgroupOf] at ha ⊢
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      exact (mem_normalizer_iff.mp (s.centralizer_le_normalizer (hSK b.2)) a).mp ha⟩
    rcases hN.eq_bot_or_eq_top with h | h
    · exfalso
      have h1 : t ∈ Φ.range.subgroupOf S := mem_subgroupOf.mpr htY
      rw [h, mem_bot] at h1
      rw [h1, orderOf_one] at ht
      omega
    · intro x hx
      have h1 : (⟨x, hx⟩ : S) ∈ Φ.range.subgroupOf S := h ▸ mem_top _
      exact mem_subgroupOf.mp h1
  obtain ⟨f, hf⟩ := exists_prime_orderOf_dvd_card' 5 h5
  obtain ⟨π, hπ⟩ := hSY f.2
  have hord : orderOf (π : Perm (Fin (n + 4))) = 5 := by
    rw [Subgroup.orderOf_coe, ← orderOf_injective Φ s.injective π, hπ, Subgroup.orderOf_coe, hf]
  have h4 := s.card_support_le_four_of_mem_centralizer (π := π) (by rw [hπ]; exact hSK f.2)
  have h5' := five_le_card_support_of_orderOf hord
  omega

end AltGenCore

namespace AltGenSetting

variable {G : Type} [Group G] [Finite G] {A R T : Subgroup G} {g : G} {n : ℕ}
  {Φ : alternatingGroup (Fin (n + 4)) →* G} (s : AltGenSetting A R T g n Φ)
include s

theorem le_of_simple_le_normalizer (h7 : 7 ≤ n) {S : Subgroup G}
    (hSN : S ≤ normalizer (A : Set G)) (hS : IsSimpleGroup S) (h2 : Even (Nat.card S))
    (h5 : 5 ∣ Nat.card S) : S ≤ A := by
  set ψ := s.psiA with hψ
  set act := actPerm ψ.symm (Or.inr h7) with hact
  have hactA : ∀ (a : G) (ha : a ∈ A), act ⟨a, le_normalizer ha⟩ =
      ((ψ.symm ⟨a, ha⟩ : alternatingGroup (Fin n)) : Perm (Fin n)) := by
    intro a ha
    refine actPerm_eq_of _ _ _ _ fun b => ?_
    have h1 : (⟨a * b * a⁻¹, (mem_normalizer_iff.mp (le_normalizer ha) b).mp b.2⟩ : A) =
        ⟨a, ha⟩ * b * ⟨a, ha⟩⁻¹ := Subtype.ext (by simp)
    simp only at h1 ⊢
    rw [h1, map_mul, map_mul, map_inv]
    rfl
  set actS : S →* Perm (Fin n) := act.comp (Subgroup.inclusion hSN) with hactS
  have hsign : ∀ x : S, actS x ∈ alternatingGroup (Fin n) := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (sign.comp actS).ker with h | h
    · exfalso
      have hinj : Function.Injective (sign.comp actS) := (MonoidHom.ker_eq_bot_iff _).mp h
      have h1 := Nat.card_le_card_of_injective _ hinj
      rw [Nat.card_eq_fintype_card (α := ℤˣ), Fintype.card_units_int] at h1
      have h3 := Nat.le_of_dvd Nat.card_pos h5
      omega
    · intro x
      exact (h ▸ mem_top x : x ∈ (sign.comp actS).ker)
  set αS : S →* A := ψ.toMonoidHom.comp (actS.codRestrict _ hsign) with hαS
  have hαact : ∀ x : S, act (Subgroup.inclusion hSN x) =
      ((ψ.symm (αS x) : alternatingGroup (Fin n)) : Perm (Fin n)) := by
    intro x
    simp only [hαS, MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.symm_apply_apply, MonoidHom.codRestrict_apply]
    rfl
  have hK : ∀ x : S, (x : G) * ((αS x : A) : G)⁻¹ ∈ centralizer (A : Set G) := by
    intro x
    have hmem : (x : G) * ((αS x : A) : G)⁻¹ ∈ normalizer (A : Set G) :=
      mul_mem (hSN x.2) (inv_mem (le_normalizer (αS x).2))
    have h1 : (⟨_, hmem⟩ : normalizer (A : Set G)) =
        Subgroup.inclusion hSN x * (⟨_, le_normalizer (αS x).2⟩)⁻¹ :=
      Subtype.ext (by simp)
    refine (actPerm_eq_one_iff ψ.symm (Or.inr h7) ⟨_, hmem⟩).mp ?_
    rw [← hact, h1, map_mul, map_inv, hαact x, hactA _ (αS x).2]
    simp
  let κ : S →* G :=
    { toFun := fun x => (x : G) * ((αS x : A) : G)⁻¹
      map_one' := by simp
      map_mul' := fun x y => by
        have hc := mem_centralizer_iff.mp (hK y) _ (inv_mem (αS x).2)
        simp only [Subgroup.coe_mul, map_mul, mul_inv_rev]
        calc (x : G) * y * ((((αS y : A) : G))⁻¹ * (((αS x : A) : G))⁻¹) =
            (x : G) * ((y : G) * ((αS y : A) : G)⁻¹ * ((αS x : A) : G)⁻¹) := by group
          _ = (x : G) * (((αS x : A) : G)⁻¹ * ((y : G) * ((αS y : A) : G)⁻¹)) := by rw [hc]
          _ = (x : G) * ((αS x : A) : G)⁻¹ * ((y : G) * ((αS y : A) : G)⁻¹) := by group }
  have hκ : ∀ x : S, κ x = (x : G) * ((αS x : A) : G)⁻¹ := fun _ => rfl
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal κ.ker with h | h
  · exfalso
    have hinj : Function.Injective κ := (MonoidHom.ker_eq_bot_iff _).mp h
    have hrange : κ.range ≤ centralizer (A : Set G) := by
      rintro _ ⟨x, rfl⟩
      exact hK x
    have e : S ≃* κ.range := MonoidHom.ofInjective hinj
    have hcard : Nat.card κ.range = Nat.card S := (Nat.card_congr e.toEquiv).symm
    exact s.not_simple_le_centralizer hrange (MulEquiv.isSimpleGroup e.symm) (hcard ▸ h2)
      (hcard ▸ h5)
  · intro x hx
    have h1 : (⟨x, hx⟩ : S) ∈ κ.ker := h ▸ mem_top _
    rw [MonoidHom.mem_ker, hκ] at h1
    have h3 : x = ((αS ⟨x, hx⟩ : A) : G) := by
      have := mul_inv_eq_one.mp h1
      exact this
    rw [h3]
    exact (αS ⟨x, hx⟩).2

theorem conj_le_of_simple (h7 : 7 ≤ n) {u x : G} (hu1 : u ≠ 1) (hu2 : u * u = 1)
    (hx : x * u * x⁻¹ ∈ centralizer (A : Set G)) {S : Subgroup G}
    (hSu : S ≤ centralizer ({u} : Set G)) (hS : IsSimpleGroup S) (h2 : Even (Nat.card S))
    (h5 : 5 ∣ Nat.card S) : S.map (MulAut.conj x).toMonoidHom ≤ A := by
  have hT1 := Lemma39.centralizer_le_normalizer_rightConjugate s.sec3.hyp 1
    (t := x * u * x⁻¹) (by rw [rightConjugate_one]; exact hx)
    (fun h => hu1 (by
      have h' : u = x⁻¹ * (x * u * x⁻¹) * x := by group
      rw [h', h]
      group))
    (by rw [sq]; calc x * u * x⁻¹ * (x * u * x⁻¹) = x * (u * u) * x⁻¹ := by group
                    _ = 1 := by rw [hu2, mul_one, mul_inv_cancel])
  rw [rightConjugate_one] at hT1
  have e : S ≃* S.map (MulAut.conj x).toMonoidHom :=
    S.equivMapOfInjective _ (MulAut.conj x).injective
  have hcard : Nat.card (S.map (MulAut.conj x).toMonoidHom) = Nat.card S :=
    (Nat.card_congr e.toEquiv).symm
  refine s.le_of_simple_le_normalizer h7 ?_ (MulEquiv.isSimpleGroup e.symm) (hcard ▸ h2)
    (hcard ▸ h5)
  rintro _ ⟨c, hc, rfl⟩
  apply hT1
  have hc' := hSu hc
  rw [mem_centralizer_singleton_iff] at hc' ⊢
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  calc x * c * x⁻¹ * (x * u * x⁻¹) = x * (c * u) * x⁻¹ := by group
    _ = x * (u * c) * x⁻¹ := by rw [hc']
    _ = x * u * x⁻¹ * (x * c * x⁻¹) := by group

end AltGenSetting

end CFSG.ComponentClassification.RankTwoAlt
