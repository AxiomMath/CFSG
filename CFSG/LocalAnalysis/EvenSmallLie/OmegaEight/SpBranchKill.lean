module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.SpBranchLike
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Stage1Sylow
public import CFSG.Monster.B.Recog.GenericTransferExtremal

public section

namespace CFSG.EvenSmallLie.OmegaEight.SpBranch

open Subgroup

variable {G : Type*} [Group G]

theorem isPGroup_sup_zpowers [Finite G] {T : Subgroup G} (hT : IsPGroup 2 T) {x : G}
    (hxN : x ∈ normalizer (T : Set G)) (hx2 : x * x ∈ T) :
    IsPGroup 2 (T ⊔ zpowers x : Subgroup G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := hT ⟨x * x, hx2⟩
  have hk' : x ^ 2 ^ (k + 1) = 1 := by
    have h1 : (x * x) ^ 2 ^ k = 1 := congrArg Subtype.val hk
    have h2 : x ^ 2 ^ (k + 1) = (x * x) ^ 2 ^ k := by
      rw [← pow_two, ← pow_mul, pow_succ, mul_comm]
    rw [h2, h1]
  have hz : IsPGroup 2 (zpowers x) := by
    refine IsPGroup.of_card (n := Nat.find (p := fun m => orderOf x = 2 ^ m) ?_) ?_
    · exact (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one hk') |>.imp
        fun _ h => h.2
    · rw [Nat.card_zpowers]
      exact Nat.find_spec (p := fun m => orderOf x = 2 ^ m) _
  exact hT.to_sup_of_normal_left' hz (zpowers_le.2 hxN)

theorem inf_centralizer_eq {t : G} {TH T : Subgroup G} (hTp : IsPGroup 2 T) (hTHT : TH ≤ T)
    (hTH : TH ≤ centralizer ({t} : Set G))
    (hTHmax : ∀ V : Subgroup G, V ≤ centralizer ({t} : Set G) → IsPGroup 2 V → TH ≤ V → V = TH) :
    T ⊓ centralizer ({t} : Set G) = TH :=
  hTHmax _ inf_le_right (hTp.to_le inf_le_left) (le_inf hTHT hTH)

theorem max_of_N5 [Finite G] {t : G} {TH T : Subgroup G} (hTHT : TH ≤ T)
    (hTH : TH ≤ centralizer ({t} : Set G))
    (hTHmax : ∀ V : Subgroup G, V ≤ centralizer ({t} : Set G) → IsPGroup 2 V → TH ≤ V → V = TH)
    (ht : t ∈ T) (ht2 : t * t = 1) (hN5 : ∀ u, Like T t u → ∃ h ∈ T, h * t * h⁻¹ = u) :
    ∀ P : Subgroup G, IsPGroup 2 P → T ≤ P → P = T := by
  intro P hP hTP
  by_contra hne
  have hlt : T < P := lt_of_le_of_ne hTP (Ne.symm hne)
  obtain ⟨n, hnP, hnN, hnT⟩ := Stage1.exists_mem_normalizer_not_mem hP hlt
  have hlike : Like T t (n * t * n⁻¹) := (like_conj hnN).2
    ⟨ht, ht2, rfl, rfl, rfl⟩
  obtain ⟨h, hhT, hht⟩ := hN5 _ hlike
  have hc : h⁻¹ * n ∈ centralizer ({t} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    have : t = (h⁻¹ * n) * t * (h⁻¹ * n)⁻¹ := by
      calc t = h⁻¹ * (h * t * h⁻¹) * h := by group
        _ = h⁻¹ * (n * t * n⁻¹) * h := by rw [hht]
        _ = (h⁻¹ * n) * t * (h⁻¹ * n)⁻¹ := by group
    calc h⁻¹ * n * t = (h⁻¹ * n) * t * (h⁻¹ * n)⁻¹ * (h⁻¹ * n) := by group
      _ = t * (h⁻¹ * n) := by rw [← this]
  have hPC : P ⊓ centralizer ({t} : Set G) = TH :=
    hTHmax _ inf_le_right (hP.to_le inf_le_left) (le_inf (hTHT.trans hTP) hTH)
  have h1 : h⁻¹ * n ∈ P := P.mul_mem (P.inv_mem (hTP hhT)) hnP
  have hmem : h⁻¹ * n ∈ TH := by
    rw [← hPC]
    exact ⟨h1, hc⟩
  apply hnT
  have : n = h * (h⁻¹ * n) := by group
  rw [this]
  exact mul_mem hhT (hTHT hmem)

theorem exists_conj_of_max [Finite G] {u : G} {A B : Subgroup G}
    (hA : A ≤ centralizer ({u} : Set G)) (hB : B ≤ centralizer ({u} : Set G))
    (hAp : IsPGroup 2 A) (hBp : IsPGroup 2 B)
    (hAmax : ∀ V : Subgroup G, V ≤ centralizer ({u} : Set G) → IsPGroup 2 V → A ≤ V → V = A)
    (hBmax : ∀ V : Subgroup G, V ≤ centralizer ({u} : Set G) → IsPGroup 2 V → B ≤ V → V = B) :
    ∃ k ∈ centralizer ({u} : Set G), B.map (MulAut.conj k).toMonoidHom = A := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := centralizer ({u} : Set G)
  have hmax : ∀ X : Subgroup G, X ≤ C → IsPGroup 2 X →
      (∀ V : Subgroup G, V ≤ C → IsPGroup 2 V → X ≤ V → V = X) →
      ∀ {Q : Subgroup C}, IsPGroup 2 Q → X.subgroupOf C ≤ Q → Q = X.subgroupOf C := by
    intro X hX hXp hXmax Q hQ hle
    have hQ' : IsPGroup 2 (Q.map C.subtype) := hQ.map _
    have hle' : X ≤ Q.map C.subtype := by
      intro x hx
      exact ⟨⟨x, hX hx⟩, hle (by simpa [mem_subgroupOf] using hx), rfl⟩
    have h := hXmax _ (map_subtype_le Q) hQ' hle'
    ext y
    constructor
    · intro hy
      have : (y : G) ∈ Q.map C.subtype := ⟨y, hy, rfl⟩
      rw [h] at this
      exact this
    · intro hy
      have : (y : G) ∈ Q.map C.subtype := by rw [h]; exact hy
      obtain ⟨z, hz, hzy⟩ := this
      rwa [Subtype.ext hzy] at hz
  let PA : Sylow 2 C := ⟨A.subgroupOf C, hAp.of_equiv (subgroupOfEquivOfLe hA).symm,
    fun hQ hle => hmax A hA hAp hAmax hQ hle⟩
  let PB : Sylow 2 C := ⟨B.subgroupOf C, hBp.of_equiv (subgroupOfEquivOfLe hB).symm,
    fun hQ hle => hmax B hB hBp hBmax hQ hle⟩
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq C PB PA
  refine ⟨k, k.2, ?_⟩
  have hk' : ∀ y : C, y ∈ (PA : Subgroup C) ↔ k⁻¹ * y * k ∈ (PB : Subgroup C) := by
    intro y
    rw [← hk, Sylow.coe_subgroup_smul, mem_pointwise_smul_iff_inv_smul_mem]
    simp
  ext x
  constructor
  · rintro ⟨y, hyB, rfl⟩
    have hy : y ∈ C := hB hyB
    have h := (hk' ⟨(k : G) * y * (k : G)⁻¹, mul_mem (mul_mem k.2 hy) (inv_mem k.2)⟩).2 (by
      change ((k⁻¹ * ⟨(k : G) * y * (k : G)⁻¹, _⟩ * k : C) : G) ∈ B
      simpa [mul_assoc] using hyB)
    exact h
  · intro hx
    have hxC : x ∈ C := hA hx
    have h := (hk' ⟨x, hxC⟩).1 hx
    refine ⟨(k : G)⁻¹ * x * k, h, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group

theorem exists_like_of_transfer [Finite G] {t : G} (hG : ∀ K : Subgroup G, K.index = 2 → t ∈ K)
    (ht2 : t * t = 1) {TH T M : Subgroup G} (hTp : IsPGroup 2 T)
    (hTmax : ∀ P : Subgroup G, IsPGroup 2 P → T ≤ P → P = T) (hTHT : TH ≤ T)
    (hTH : TH ≤ centralizer ({t} : Set G))
    (hTHmax : ∀ V : Subgroup G, V ≤ centralizer ({t} : Set G) → IsPGroup 2 V → TH ≤ V → V = TH)
    (hMT : M ≤ T) (hM : M.relIndex T = 2) : ∃ u ∈ M, Like T t u := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let T' : Sylow 2 G := ⟨T, hTp, fun hQ hle => hTmax _ hQ hle⟩
  obtain ⟨g, hgM, hodd⟩ := CFSG.Monster.B.Recog.exists_conj_mem_odd_relIndex_of_transfer T' hM
    (by rw [pow_two, ht2]) hG
  set u := g * t * g⁻¹ with hu
  refine ⟨u, hgM, ?_⟩
  have hTC : T ⊓ centralizer ({t} : Set G) = TH := inf_centralizer_eq hTp hTHT hTH hTHmax
  have hA : ∀ V : Subgroup G, V ≤ centralizer ({u} : Set G) → IsPGroup 2 V →
      T ⊓ centralizer ({u} : Set G) ≤ V → V = T ⊓ centralizer ({u} : Set G) := by
    intro V hV hVp hle
    have hmul := relIndex_mul_relIndex _ _ _ hle hV
    rw [inf_relIndex_right] at hmul
    have hd : (T ⊓ centralizer ({u} : Set G)).relIndex V ∣ Nat.card V := relIndex_dvd_card _ _
    obtain ⟨m, hm⟩ := hVp.exists_card_eq
    rw [hm] at hd
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hd
    have h1 : (T ⊓ centralizer ({u} : Set G)).relIndex V = 1 := by
      rcases j with _ | j
      · simpa using hj
      · exfalso
        rw [← hmul, hj, pow_succ, mul_assoc] at hodd
        exact Nat.not_odd_iff_even.2 even_two (Nat.odd_mul.1 (Nat.odd_mul.1 hodd).2).1
    exact le_antisymm (relIndex_eq_one.1 h1) hle
  have hB : ∀ V : Subgroup G, V ≤ centralizer ({u} : Set G) → IsPGroup 2 V →
      TH.map (MulAut.conj g).toMonoidHom ≤ V → V = TH.map (MulAut.conj g).toMonoidHom := by
    intro V hV hVp hle
    set W := V.map (MulAut.conj g⁻¹).toMonoidHom
    have hW : W ≤ centralizer ({t} : Set G) := by
      rintro _ ⟨v, hv, rfl⟩
      have hvu := mem_centralizer_singleton_iff.1 (hV hv)
      rw [mem_centralizer_singleton_iff]
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      calc g⁻¹ * v * g * t = g⁻¹ * (v * (g * t * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * t * g⁻¹) * v) * g := by rw [← hu, hvu]
        _ = t * (g⁻¹ * v * g) := by group
    have hWp : IsPGroup 2 W := hVp.map _
    have hTHW : TH ≤ W := by
      intro x hx
      refine ⟨g * x * g⁻¹, hle ⟨x, hx, rfl⟩, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      group
    have hWeq := hTHmax W hW hWp hTHW
    ext y
    constructor
    · intro hy
      have : g⁻¹ * y * g ∈ TH := by
        rw [← hWeq]; exact ⟨y, hy, by simp⟩
      exact ⟨g⁻¹ * y * g, this, by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group⟩
    · intro hy; exact hle hy
  have hBle : TH.map (MulAut.conj g).toMonoidHom ≤ centralizer ({u} : Set G) := by
    rintro _ ⟨x, hx, rfl⟩
    have hxt := mem_centralizer_singleton_iff.1 (hTH hx)
    rw [mem_centralizer_singleton_iff]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hu]
    calc g * x * g⁻¹ * (g * t * g⁻¹) = g * (x * t) * g⁻¹ := by group
      _ = g * (t * x) * g⁻¹ := by rw [hxt]
      _ = g * t * g⁻¹ * (g * x * g⁻¹) := by group
  obtain ⟨k, hkC, hk⟩ := exists_conj_of_max inf_le_right hBle (hTp.to_le inf_le_left)
    ((hTp.to_le hTHT).map _) hA hB
  have hmap : (T ⊓ centralizer ({t} : Set G)).map (MulAut.conj (k * g)).toMonoidHom =
      T ⊓ centralizer ({u} : Set G) := by
    rw [hTC, ← hk, map_map]
    congr 1
    ext x
    simp [MulAut.conj_apply, mul_assoc]
  have hku : k * g * t * (k * g)⁻¹ = u := by
    have hku' := mem_centralizer_singleton_iff.1 hkC
    calc k * g * t * (k * g)⁻¹ = k * u * k⁻¹ := by rw [hu]; group
      _ = u := by rw [hku']; group
  refine ⟨hMT hgM, by
    rw [hu, show g * t * g⁻¹ * (g * t * g⁻¹) = g * (t * t) * g⁻¹ by group, ht2]; group, ?_, ?_, ?_⟩
  · rw [← hmap, card_map]
  · rw [← hmap, nInv_map]
  · rw [← hmap, nOrd4_map]

theorem false_of_N5 [Finite G] {t : G} (hG : ∀ K : Subgroup G, K.index = 2 → t ∈ K)
    (ht2 : t * t = 1) {TH T M : Subgroup G} (hTp : IsPGroup 2 T) (hTHT : TH ≤ T)
    (hTH : TH ≤ centralizer ({t} : Set G))
    (hTHmax : ∀ V : Subgroup G, V ≤ centralizer ({t} : Set G) → IsPGroup 2 V → TH ≤ V → V = TH)
    (ht : t ∈ T) (hN5 : ∀ u, Like T t u → ∃ h ∈ T, h * t * h⁻¹ = u)
    (hMT : M ≤ T) (hM : M.relIndex T = 2) (hMn : ∀ h ∈ T, ∀ x ∈ M, h * x * h⁻¹ ∈ M)
    (htM : t ∉ M) : False := by
  have hTmax := max_of_N5 hTHT hTH hTHmax ht ht2 hN5
  obtain ⟨u, huM, hu⟩ := exists_like_of_transfer hG ht2 hTp hTmax hTHT hTH hTHmax hMT hM
  obtain ⟨h, hhT, rfl⟩ := hN5 u hu
  apply htM
  have := hMn h⁻¹ (inv_mem hhT) _ huM
  simpa [mul_assoc] using this

theorem exists_step [Finite G] {T : Subgroup G}
    (hT : ¬ ∀ P : Subgroup G, IsPGroup 2 P → T ≤ P → P = T) :
    ∃ x ∈ normalizer (T : Set G), x ∉ T ∧ x * x ∈ T := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  push Not at hT
  obtain ⟨P, hP, hTP, hne⟩ := hT
  obtain ⟨n, hnP, hnN, hnT⟩ := Stage1.exists_mem_normalizer_not_mem hP (lt_of_le_of_ne hTP hne.symm)
  obtain ⟨k, hk⟩ := hP ⟨n, hnP⟩
  have hk' : n ^ 2 ^ k = 1 := congrArg Subtype.val hk
  have hex : ∃ m, n ^ 2 ^ m ∈ T := ⟨k, by rw [hk']; exact one_mem T⟩
  set m := Nat.find hex with hm
  have hm0 : m ≠ 0 := by
    intro h0
    have := Nat.find_spec hex
    rw [← hm, h0, pow_zero, pow_one] at this
    exact hnT this
  obtain ⟨j, hj⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
  refine ⟨n ^ 2 ^ j, Subgroup.pow_mem _ hnN _, fun h => ?_, ?_⟩
  · have := Nat.find_min hex (show j < m by omega)
    exact this h
  · have := Nat.find_spec hex
    rw [← hm, hj, pow_succ, pow_mul, pow_two] at this
    exact this

end CFSG.EvenSmallLie.OmegaEight.SpBranch
