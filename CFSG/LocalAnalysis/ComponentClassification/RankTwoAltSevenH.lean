module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltSevenSylow
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltSmallFactsGW

public section

namespace CFSG.ComponentClassification.RankTwoAlt

open Equiv Equiv.Perm Subgroup CFSG.ABGLocalTools

theorem kOf_injective : Function.Injective kOf := by
  intro i j h
  revert i j
  decide

theorem card_kleinFour : Nat.card kleinFour = 4 := by
  have hbij : Function.Bijective (fun i : Fin 4 => (⟨kOf i, kOf_mem i⟩ : kleinFour)) :=
    ⟨fun i j h => kOf_injective (congrArg Subtype.val h), fun ⟨x, hx⟩ => by
      obtain ⟨i, rfl⟩ := exists_kOf_of_mem_kleinFour hx
      exact ⟨i, rfl⟩⟩
  rw [← Nat.card_eq_of_bijective _ hbij, Nat.card_eq_fintype_card, Fintype.card_fin]

theorem card_rootV {n : ℕ} (h : 4 ≤ n) : Nat.card (rootV n) = 4 := by
  rw [rootV, dite_eq_left h]
  have hle : kleinFour.map (viaEmbeddingHom (fourEmb h)) ≤ alternatingGroup (Fin n) := by
    rintro _ ⟨k, hk, rfl⟩
    exact viaEmbeddingHom_mem_alternatingGroup' _ (kleinFour_le_alternatingGroup hk)
  have e1 := (subgroupOfEquivOfLe hle).toEquiv
  rw [show ((kleinFour.map (viaEmbeddingHom (fourEmb h))).comap
      (alternatingGroup (Fin n)).subtype) = (kleinFour.map (viaEmbeddingHom (fourEmb h))).subgroupOf
        (alternatingGroup (Fin n)) from rfl, Nat.card_congr e1,
    card_map_of_injective (viaEmbeddingHom_injective _), card_kleinFour]

namespace Seven

variable {G : Type} [Group G] {A B : Subgroup G}

@[expose] noncomputable def w (ψA : A ≃* alternatingGroup (Fin 7)) : G := (ψA.symm a123 : G)

@[expose] noncomputable def u (ψA : A ≃* alternatingGroup (Fin 7)) : G := (ψA.symm a456 : G)

@[expose] noncomputable def x (ψA : A ≃* alternatingGroup (Fin 7)) : G := (ψA.symm aπx : G)

@[expose] noncomputable def v (ψB : B ≃* alternatingGroup (Fin 7)) : G := (ψB.symm a123 : G)

@[expose] noncomputable def T (ψA : A ≃* alternatingGroup (Fin 7)) : Subgroup G :=
  ((rootV 7).map ψA.symm.toMonoidHom).map A.subtype

@[expose] noncomputable def VF (ψA : A ≃* alternatingGroup (Fin 7)) : Subgroup G :=
  (T ψA).map (MulAut.conj (x ψA)⁻¹).toMonoidHom

@[expose] noncomputable def H7 (ψA : A ≃* alternatingGroup (Fin 7))
    (ψB : B ≃* alternatingGroup (Fin 7)) : Subgroup G :=
  centralizer ({w ψA} : Set G) ⊓ centralizer ({v ψB} : Set G)

variable (ψA : A ≃* alternatingGroup (Fin 7)) (ψB : B ≃* alternatingGroup (Fin 7))

theorem x_mul_w : x ψA * w ψA * (x ψA)⁻¹ = u ψA := by
  have h0 : aπx * a123 * aπx⁻¹ = a456 := by
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
    exact πx_conj_p123
  have h : ψA.symm aπx * ψA.symm a123 * (ψA.symm aπx)⁻¹ = ψA.symm a456 := by
    rw [← map_inv, ← map_mul, ← map_mul, h0]
  exact congrArg Subtype.val h

theorem w_mem : w ψA ∈ A := (ψA.symm a123).2
theorem u_mem : u ψA ∈ A := (ψA.symm a456).2
theorem x_mem : x ψA ∈ A := (ψA.symm aπx).2
theorem v_mem : v ψB ∈ B := (ψB.symm a123).2

theorem T_le : T ψA ≤ A := by
  rintro _ ⟨a, -, rfl⟩
  exact a.2

theorem rootV7_cases {k : alternatingGroup (Fin 7)} (hk : k ∈ rootV 7) :
    (k : Perm (Fin 7)) = 1 ∨ (k : Perm (Fin 7)) = swap 0 1 * swap 2 3 ∨
      (k : Perm (Fin 7)) = swap 0 2 * swap 1 3 ∨
        (k : Perm (Fin 7)) = swap 0 1 * swap 2 3 * (swap 0 2 * swap 1 3) := by
  obtain ⟨k', hk', hkk⟩ := (mem_rootV_iff (by norm_num) k).mp hk
  obtain ⟨i, rfl⟩ := exists_kOf_of_mem_kleinFour hk'
  rw [← hkk]
  fin_cases i <;> simp [kOf, map_mul, viaEmbeddingHom_swap] <;> decide

theorem restrictO_p456 : restrictO p456 = p456 := by
  have hst : StabO p456 := by decide
  ext i
  by_cases hi : 4 ≤ (i : ℕ)
  · rw [restrictO_apply_of_ge hst hi]
  · rw [restrictO_apply_of_lt hst (by omega)]
    revert hi
    revert i
    decide

variable {ψA ψB}

theorem stab_a456 : ∀ i : Fin 7, (i : ℕ) < 4 → ((ψA (ψA.symm a456) : Perm (Fin 7)) i : ℕ) < 4 := by
  rw [MulEquiv.apply_symm_apply]
  decide

theorem stab_a456_inv :
    ∀ i : Fin 7, (i : ℕ) < 4 → ((ψA (ψA.symm a456)⁻¹ : Perm (Fin 7)) i : ℕ) < 4 := by
  rw [map_inv, MulEquiv.apply_symm_apply]
  decide

theorem u_normalizes (hco : AltCoords 7 A B ψA ψB) : u ψA ∈ normalizer (B : Set G) := by
  obtain ⟨-, -, -, -, hC1, -⟩ := hco
  rw [mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    exact (hC1 _ stab_a456 ⟨h, hh⟩).1
  · intro hh
    have hb := (hC1 _ stab_a456_inv ⟨_, hh⟩).1
    simpa [u, mul_assoc] using hb

theorem actPerm_u (hco : AltCoords 7 A B ψA ψB) :
    actPerm ψB (Or.inr le_rfl) ⟨u ψA, u_normalizes hco⟩ = p456 := by
  have hC1 := hco.2.2.2.2.1
  apply actPerm_eq_of
  intro b
  obtain ⟨hb, hbe⟩ := hC1 _ stab_a456 b
  rw [MulEquiv.apply_symm_apply] at hbe
  rw [show ((a456 : alternatingGroup (Fin 7)) : Perm (Fin 7)) = p456 from rfl, restrictO_p456]
    at hbe
  exact hbe

theorem actPerm_v :
    actPerm ψB (Or.inr le_rfl) ⟨v ψB, le_normalizer (v_mem ψB)⟩ = p123 := by
  apply actPerm_eq_of
  intro b
  have h : (⟨v ψB * b * (v ψB)⁻¹, (mem_normalizer_iff.mp (le_normalizer (v_mem ψB)) b).mp b.2⟩ :
      B) = ψB.symm a123 * b * (ψB.symm a123)⁻¹ := Subtype.ext rfl
  rw [h, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
  rfl

theorem v_mem_centralizer_A (hco : AltCoords 7 A B ψA ψB) : v ψB ∈ centralizer (A : Set G) :=
  hco.2.2.2.1 ⟨ψB.symm a123, ⟨a123, a123_mem_rootAlt, rfl⟩, rfl⟩

theorem card_T : Nat.card (T ψA) = 4 := by
  rw [T, card_map_of_injective A.subtype_injective, card_map_of_injective ψA.symm.injective,
    card_rootV (by norm_num)]

theorem card_VF : Nat.card (VF ψA) = 4 := by
  rw [VF, card_map_of_injective (MulAut.conj _).injective, card_T]

theorem mul_self_of_mem_T {t : G} (ht : t ∈ T ψA) : t * t = 1 := by
  obtain ⟨_, ⟨k, hk, rfl⟩, rfl⟩ := ht
  have hk2 : k * k = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_one]
    rcases Seven.rootV7_cases hk with h | h | h | h <;> rw [h] <;> decide
  show ((ψA.symm k : A) : G) * (ψA.symm k : A) = 1
  rw [← Subgroup.coe_mul, ← map_mul, hk2, map_one, Subgroup.coe_one]

theorem VF_le_H7 (hco : AltCoords 7 A B ψA ψB) : VF ψA ≤ H7 ψA ψB := by
  rintro _ ⟨_, ⟨_, ⟨k, hk, rfl⟩, rfl⟩, rfl⟩
  have hs : (x ψA)⁻¹ * ((ψA.symm k : A) : G) * ((x ψA)⁻¹)⁻¹ =
      ((ψA.symm (aπx⁻¹ * k * aπx) : A) : G) := by
    rw [inv_inv, map_mul, map_mul, map_inv]
    rfl
  show (x ψA)⁻¹ * ((ψA.symm k : A) : G) * ((x ψA)⁻¹)⁻¹ ∈ H7 ψA ψB
  rw [hs]
  refine ⟨mem_centralizer_singleton_iff.mpr ?_, mem_centralizer_singleton_iff.mpr ?_⟩
  · have hc : aπx⁻¹ * k * aπx * a123 = a123 * (aπx⁻¹ * k * aπx) := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rcases Seven.rootV7_cases hk with h | h | h | h <;> rw [h] <;> decide
    show ((ψA.symm (aπx⁻¹ * k * aπx) : A) : G) * (ψA.symm a123 : A) =
      (ψA.symm a123 : A) * (ψA.symm (aπx⁻¹ * k * aπx) : A)
    rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul, hc]
  · exact (mem_centralizer_iff.mp (v_mem_centralizer_A hco)) _
      (ψA.symm (aπx⁻¹ * k * aπx)).2

theorem card_le_card_of_isSylowOf [Finite G] {p : ℕ} [Fact p.Prime] {S K Q : Subgroup G}
    (hS : IsSylowOf p S K) (hQK : Q ≤ K) (hQ : IsPGroup p Q) : Nat.card Q ≤ Nat.card S := by
  obtain ⟨S', hS'⟩ := (hQ.comap_subtype (K := K)).exists_le_sylow
  have h1 : Nat.card (Q.subgroupOf K) = Nat.card Q :=
    Nat.card_congr (subgroupOfEquivOfLe hQK).toEquiv
  have h2 : Nat.card (Q.subgroupOf K) ≤ Nat.card (S' : Subgroup K) := card_le_of_le hS'
  rw [hS.card_eq, ← Sylow.card_eq_multiplicity S', ← h1]
  exact h2

theorem card_le_four_of_isPGroup [Finite G] (hco : AltCoords 7 A B ψA ψB)
    (ht1B : ∀ t ∈ centralizer (B : Set G), t * t = 1 → t ≠ 1 →
      centralizer ({t} : Set G) ≤ normalizer (B : Set G))
    {s : G} (hs : s ∈ VF ψA) (hs1 : s ≠ 1) {P : Subgroup G} (hP : IsPGroup 2 P)
    (hPH : P ≤ H7 ψA ψB) (hPs : P ≤ centralizer ({s} : Set G)) : Nat.card P ≤ 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨t, htT, rfl⟩ := hs
  set φ : G →* G := (MulAut.conj (x ψA)).toMonoidHom with hφ
  have hφapp : ∀ g, φ g = x ψA * g * (x ψA)⁻¹ := fun g => rfl
  have key : ∀ a b : G, a * b = b * a → φ a * φ b = φ b * φ a := fun a b h => by
    rw [← map_mul, ← map_mul, h]
  have hφs : φ ((MulAut.conj (x ψA)⁻¹).toMonoidHom t) = t := by
    rw [hφapp]
    show x ψA * ((x ψA)⁻¹ * t * ((x ψA)⁻¹)⁻¹) * (x ψA)⁻¹ = t
    group
  have hφw : φ (w ψA) = u ψA := by rw [hφapp, x_mul_w]
  have hφv : φ (v ψB) = v ψB := by
    rw [hφapp, (mem_centralizer_iff.mp (v_mem_centralizer_A hco)) _ (x_mem ψA),
      mul_inv_cancel_right]
  have htC : t ∈ centralizer (B : Set G) := hco.1.le htT
  have ht2 : t * t = 1 := mul_self_of_mem_T htT
  have ht1 : t ≠ 1 := fun h => hs1 (by rw [h, map_one])
  set P' := P.map φ with hP'
  have hP'p : IsPGroup 2 P' := hP.map φ
  have hP't : P' ≤ centralizer ({t} : Set G) := by
    rintro _ ⟨p, hp, rfl⟩
    rw [mem_centralizer_singleton_iff, ← hφs]
    exact key _ _ (mem_centralizer_singleton_iff.mp (hPs hp))
  have hP'u : P' ≤ centralizer ({u ψA} : Set G) := by
    rintro _ ⟨p, hp, rfl⟩
    rw [mem_centralizer_singleton_iff, ← hφw]
    exact key _ _ (mem_centralizer_singleton_iff.mp (mem_inf.mp (hPH hp)).1)
  have hP'v : P' ≤ centralizer ({v ψB} : Set G) := by
    rintro _ ⟨p, hp, rfl⟩
    rw [mem_centralizer_singleton_iff, ← hφv]
    exact key _ _ (mem_centralizer_singleton_iff.mp (mem_inf.mp (hPH hp)).2)
  have hP'N : P' ≤ normalizer (B : Set G) := hP't.trans (ht1B t htC ht2 ht1)
  have hP'C := le_centralizer_of_isPGroup ψB (u_normalizes hco) (le_normalizer (v_mem ψB))
    (actPerm_u hco) actPerm_v hP'p hP'N hP'u hP'v
  have h1 : Nat.card P = Nat.card P' := (card_map_of_injective (MulAut.conj _).injective).symm
  rw [h1, ← card_T (ψA := ψA)]
  exact card_le_card_of_isSylowOf hco.1 hP'C hP'p

theorem isSylowOf_VF [Finite G] (hco : AltCoords 7 A B ψA ψB)
    (ht1B : ∀ t ∈ centralizer (B : Set G), t * t = 1 → t ≠ 1 →
      centralizer ({t} : Set G) ≤ normalizer (B : Set G)) :
    IsSylowOf 2 (VF ψA) (H7 ψA ψB) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hVp : IsPGroup 2 (VF ψA) := IsPGroup.of_card (n := 2) (by rw [card_VF]; norm_num)
  have hVH := VF_le_H7 hco (ψB := ψB)
  obtain ⟨S', hS'⟩ := (hVp.comap_subtype (K := H7 ψA ψB)).exists_le_sylow
  set S := (S' : Subgroup (H7 ψA ψB)).map (H7 ψA ψB).subtype
  have hS : IsSylowOf 2 S (H7 ψA ψB) := ⟨S', rfl⟩
  have hVS : VF ψA ≤ S := fun y hy => ⟨⟨y, hVH hy⟩, hS' (mem_subgroupOf.mpr hy), rfl⟩
  by_cases hSV : S ≤ VF ψA
  · rwa [← le_antisymm hSV hVS]
  exfalso
  obtain ⟨a, haS, haN, haV⟩ := exists_mem_normalizer_of_not_le hS.isPGroup hVS hSV
  have hQp : IsPGroup 2 (S ⊓ normalizer (VF ψA : Set G) : Subgroup G) :=
    hS.isPGroup.to_le inf_le_left
  obtain ⟨s, hs, hs1, hQs⟩ := exists_mem_ne_one_le_centralizer card_VF hQp inf_le_right
  have h4 := card_le_four_of_isPGroup hco ht1B hs hs1 hQp (inf_le_left.trans hS.le) hQs
  have hlt : VF ψA < S ⊓ normalizer (VF ψA : Set G) :=
    lt_of_le_of_ne (le_inf hVS le_normalizer) fun h => haV (h ▸ mem_inf.mpr ⟨haS, haN⟩)
  have := card_lt_of_lt hlt
  rw [card_VF] at this
  omega

theorem mul_self_of_mem_VF {s : G} (hs : s ∈ VF ψA) : s * s = 1 := by
  obtain ⟨t, ht, rfl⟩ := hs
  have h := mul_self_of_mem_T ht
  show (x ψA)⁻¹ * t * ((x ψA)⁻¹)⁻¹ * ((x ψA)⁻¹ * t * ((x ψA)⁻¹)⁻¹) = 1
  calc (x ψA)⁻¹ * t * ((x ψA)⁻¹)⁻¹ * ((x ψA)⁻¹ * t * ((x ψA)⁻¹)⁻¹)
      = (x ψA)⁻¹ * (t * t) * x ψA := by group
    _ = 1 := by rw [h]; group

theorem hasDihedralSylowTwo_H7 [Finite G] (hco : AltCoords 7 A B ψA ψB)
    (ht1B : ∀ t ∈ centralizer (B : Set G), t * t = 1 → t ≠ 1 →
      centralizer ({t} : Set G) ≤ normalizer (B : Set G)) :
    CFSG.GorensteinWalter.HasDihedralSylowTwo (H7 ψA ψB) := by
  obtain ⟨S, hS⟩ := isSylowOf_VF hco ht1B
  have hcard : Nat.card (S : Subgroup (H7 ψA ψB)) = 4 := by
    rw [← card_VF (ψA := ψA), ← hS, card_map_of_injective (H7 ψA ψB).subtype_injective]
  have hsq : ∀ y : (S : Subgroup (H7 ψA ψB)), y ^ 2 = 1 := by
    intro y
    have hy : ((y : H7 ψA ψB) : G) ∈ VF ψA := hS ▸ ⟨y, y.2, rfl⟩
    apply Subtype.ext
    apply Subtype.ext
    simpa [sq] using mul_self_of_mem_VF hy
  have hK : IsKleinFour (S : Subgroup (H7 ψA ψB)) := by
    refine ⟨hcard, ?_⟩
    rcases (Nat.dvd_prime Nat.prime_two).mp (Monoid.exponent_dvd_of_forall_pow_eq_one hsq) with
      h | h
    · have : Subsingleton (S : Subgroup (H7 ψA ψB)) := Monoid.exp_eq_one_iff.mp h
      have := Nat.card_of_subsingleton (1 : (S : Subgroup (H7 ψA ψB)))
      omega
    · exact h
  obtain ⟨e⟩ := IsKleinFour.nonempty_mulEquiv (G₁ := (S : Subgroup (H7 ψA ψB)))
    (G₂ := DihedralGroup 2)
  exact hasDihedralSylowTwo_of_equiv S (m := 1) le_rfl e

theorem actPerm_inner (c : alternatingGroup (Fin 7)) :
    actPerm ψB (Or.inr le_rfl) ⟨(ψB.symm c : G), le_normalizer (ψB.symm c).2⟩ = c := by
  apply actPerm_eq_of
  intro b
  have h : (⟨(ψB.symm c : G) * b * (ψB.symm c : G)⁻¹,
      (mem_normalizer_iff.mp (le_normalizer (ψB.symm c).2) b).mp b.2⟩ : B) =
        ψB.symm c * b * (ψB.symm c)⁻¹ := Subtype.ext rfl
  rw [h, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
  rfl

theorem actPerm_of_stab (hco : AltCoords 7 A B ψA ψB) {σ : alternatingGroup (Fin 7)}
    (hσ : ∀ i : Fin 7, (i : ℕ) < 4 → ((σ : Perm (Fin 7)) i : ℕ) < 4)
    (hσi : ∀ i : Fin 7, (i : ℕ) < 4 →
      (((σ⁻¹ : alternatingGroup (Fin 7)) : Perm (Fin 7)) i : ℕ) < 4) :
    ∃ hN : (ψA.symm σ : G) ∈ normalizer (B : Set G),
      actPerm ψB (Or.inr le_rfl) ⟨_, hN⟩ = restrictO (σ : Perm (Fin 7)) := by
  have hC1 := hco.2.2.2.2.1
  have h1 : ∀ i : Fin 7, (i : ℕ) < 4 → ((ψA (ψA.symm σ) : Perm (Fin 7)) i : ℕ) < 4 := by
    rw [MulEquiv.apply_symm_apply]; exact hσ
  have h2 : ∀ i : Fin 7, (i : ℕ) < 4 → ((ψA (ψA.symm σ)⁻¹ : Perm (Fin 7)) i : ℕ) < 4 := by
    rw [map_inv, MulEquiv.apply_symm_apply]; exact hσi
  have hN : (ψA.symm σ : G) ∈ normalizer (B : Set G) := by
    rw [mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      exact (hC1 _ h1 ⟨h, hh⟩).1
    · intro hh
      have hb := (hC1 _ h2 ⟨_, hh⟩).1
      simpa [mul_assoc] using hb
  refine ⟨hN, actPerm_eq_of _ _ _ _ fun b => ?_⟩
  obtain ⟨hb, hbe⟩ := hC1 _ h1 b
  rw [MulEquiv.apply_symm_apply] at hbe
  exact hbe

end Seven

end CFSG.ComponentClassification.RankTwoAlt
