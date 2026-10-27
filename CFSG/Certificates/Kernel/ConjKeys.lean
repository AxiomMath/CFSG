module

public import CFSG.Sporadic.Schreier.PairChain

public section

namespace CFSG.KC.ConjKeys

open Subgroup

variable {G : Type*} [Group G]

theorem conj_eq_of_mul_eq {x a b k l : G} (he : a * k = b * l) (hk : k * x = x * k)
    (hl : l * x = x * l) : a * x * a⁻¹ = b * x * b⁻¹ := by
  have ha : a = b * l * k⁻¹ := by
    rw [← he]
    group
  have hk' : k⁻¹ * x * k = x := by
    rw [mul_assoc, ← hk]
    group
  have hl' : l * x * l⁻¹ = x := by
    rw [hl]
    group
  rw [ha]
  calc b * l * k⁻¹ * x * (b * l * k⁻¹)⁻¹ = b * l * (k⁻¹ * x * k) * l⁻¹ * b⁻¹ := by group
    _ = b * (l * x * l⁻¹) * b⁻¹ := by
        rw [hk']
        group
    _ = b * x * b⁻¹ := by rw [hl']

theorem card_mul_le_of_conj_keys (H : Subgroup G) [Finite H] (x : G) {N : ℕ} (c : ℕ → G)
    (hc : ∀ j < N, c j ∈ H) {α : Type*} (key : G → α)
    (hk : ∀ i < N, ∀ j < N, key (c i * x * (c i)⁻¹) = key (c j * x * (c j)⁻¹) → i = j) :
    N * Nat.card ↥(H ⊓ centralizer ({x} : Set G)) ≤ Nat.card H := by
  let f : Fin N × ↥(H ⊓ centralizer ({x} : Set G)) → H := fun p =>
    ⟨c p.1 * p.2, H.mul_mem (hc p.1 p.1.2) (mem_inf.mp p.2.2).1⟩
  have hf : Function.Injective f := by
    rintro ⟨i, k⟩ ⟨j, l⟩ hij
    have he : c i * (k : G) = c j * l := congrArg Subtype.val hij
    have hconj : c i * x * (c i)⁻¹ = c j * x * (c j)⁻¹ :=
      conj_eq_of_mul_eq he (mem_centralizer_singleton_iff.mp (mem_inf.mp k.2).2)
        (mem_centralizer_singleton_iff.mp (mem_inf.mp l.2).2)
    have hij' : i = j := Fin.ext (hk i i.2 j j.2 (congrArg key hconj))
    subst hij'
    have hkl : k = l := Subtype.ext (mul_left_cancel he)
    rw [hkl]
  have h := Nat.card_le_card_of_injective f hf
  rwa [Nat.card_prod, Nat.card_eq_fintype_card (α := Fin N), Fintype.card_fin] at h

theorem lcm_dvd_card {K : Subgroup G} [Finite K] :
    ∀ (Ks : List (Subgroup G)), (∀ L ∈ Ks, L ≤ K) →
      (Ks.map fun L : Subgroup _ => Nat.card L).foldr Nat.lcm 1 ∣ Nat.card K
  | [], _ => one_dvd _
  | L :: Ks, h => by
    rw [List.map_cons, List.foldr_cons]
    exact Nat.lcm_dvd (Subgroup.card_dvd_of_le (h L List.mem_cons_self))
      (lcm_dvd_card Ks fun L' hL' => h L' (List.mem_cons_of_mem L hL'))

theorem card_inf_centralizer_eq_of_conj_keys (H : Subgroup G) [Finite H] (x : G) {N m : ℕ}
    (hNm : N * m = Nat.card H) (c : ℕ → G) (hc : ∀ j < N, c j ∈ H) {α : Type*} (key : G → α)
    (hk : ∀ i < N, ∀ j < N, key (c i * x * (c i)⁻¹) = key (c j * x * (c j)⁻¹) → i = j)
    (Ks : List (Subgroup G)) (hK : ∀ L ∈ Ks, L ≤ H ⊓ centralizer ({x} : Set G))
    (hm : (Ks.map fun L : Subgroup _ => Nat.card L).foldr Nat.lcm 1 = m) :
    Nat.card ↥(H ⊓ centralizer ({x} : Set G)) = m := by
  have : Finite ↥(H ⊓ centralizer ({x} : Set G)) :=
    Finite.of_injective _ (Subgroup.inclusion_injective (inf_le_left (b := centralizer {x})))
  have hle := card_mul_le_of_conj_keys H x c hc key hk
  have hdvd := lcm_dvd_card Ks hK
  rw [hm] at hdvd
  have hpos : 0 < Nat.card ↥(H ⊓ centralizer ({x} : Set G)) := Nat.card_pos
  have hHpos : 0 < Nat.card H := Nat.card_pos
  have hN : 0 < N := by
    rcases Nat.eq_zero_or_pos N with rfl | h
    · rw [zero_mul] at hNm
      omega
    · exact h
  have h1 := Nat.le_of_dvd hpos hdvd
  have hle' : N * Nat.card ↥(H ⊓ centralizer ({x} : Set G)) ≤ N * m := by
    rw [hNm]
    exact hle
  have h2 : Nat.card ↥(H ⊓ centralizer ({x} : Set G)) ≤ m := Nat.le_of_mul_le_mul_left hle' hN
  omega

theorem eq_inf_centralizer_of_conj_keys (H : Subgroup G) [Finite H] (x : G) {N : ℕ} (c : ℕ → G)
    (hc : ∀ j < N, c j ∈ H) {α : Type*} (key : G → α)
    (hk : ∀ i < N, ∀ j < N, key (c i * x * (c i)⁻¹) = key (c j * x * (c j)⁻¹) → i = j)
    {K : Subgroup G} (hK : K ≤ H ⊓ centralizer ({x} : Set G)) (hcard : N * Nat.card K = Nat.card H) :
    K = H ⊓ centralizer ({x} : Set G) := by
  have hcK := card_inf_centralizer_eq_of_conj_keys H x hcard c hc key hk [K]
    (fun L hL => by rw [List.mem_singleton.mp hL]; exact hK) (by simp)
  have : Finite ↥(H ⊓ centralizer ({x} : Set G)) :=
    Finite.of_injective _ (Subgroup.inclusion_injective (inf_le_left (b := centralizer {x})))
  exact Subgroup.eq_of_le_of_card_ge hK hcK.le

open CFSG.Certificates CFSG.Certificates.ChainArrays CFSG.Certificates.Native
  CFSG.Monster.B.Co2 CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.PairNative

theorem countW_eq_of_conj_keys {n : ℕ} {Q : RawSchreierDatum n} {O S : Array (Array ℕ)}
    {base : Array ℕ} {W : Array (List ℤ)} {chunks : ℕ} (hA : ChainArrays Q O S base W)
    (hc0 : 0 < chunks) (h : rawChainOK n O S base W chunks = true) {groups : List (List ℕ)}
    (hg : groups.flatten = List.range Q.baseCount) {f : List (Array ℕ) → Bool}
    {x : Equiv.Perm (Fin n)}
    (hfP : ∀ w g, RepW n w g → g ∈ Q.originalSubgroup → (f w = true ↔ g * x = x * g))
    {N m : ℕ} (hNm : N * m = Nat.card Q.originalSubgroup) (c : ℕ → Equiv.Perm (Fin n))
    (hc : ∀ j < N, c j ∈ Q.originalSubgroup) {α : Type*} (key : Equiv.Perm (Fin n) → α)
    (hk : ∀ i < N, ∀ j < N, key (c i * x * (c i)⁻¹) = key (c j * x * (c j)⁻¹) → i = j)
    (Ks : List (Subgroup (Equiv.Perm (Fin n))))
    (hK : ∀ L ∈ Ks, L ≤ Q.originalSubgroup ⊓ centralizer ({x} : Set (Equiv.Perm (Fin n))))
    (hm : (Ks.map fun L : Subgroup _ => Nat.card L).foldr Nat.lcm 1 = m) :
    countW f (blocksOf n (rawLevels n S base) groups) [] = m := by
  classical
  rw [← card_eq_countW hA hc0 h hg hfP (Pr := fun g => g * x = x * g),
    ← card_inf_centralizer_eq_of_conj_keys Q.originalSubgroup x hNm c hc key hk Ks hK hm]
  refine Nat.card_congr ⟨fun y => ⟨y.1, mem_inf.mpr ⟨y.1.2, ?_⟩⟩,
    fun y => ⟨⟨y.1, (mem_inf.mp y.2).1⟩, ?_⟩, fun _ => rfl, fun _ => rfl⟩
  · exact mem_centralizer_singleton_iff.mpr y.2
  · exact mem_centralizer_singleton_iff.mp (mem_inf.mp y.2).2

end CFSG.KC.ConjKeys

end
