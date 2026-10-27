module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreRL2Small

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

namespace PartC

variable {G : Type} [Group G] {T Q P₁ : Subgroup G} {e u y : G}

@[expose] def pairStabilizer (hc : PartC T Q P₁ e u) (z : G) : Subgroup G where
  carrier := {g | g * z * g⁻¹ = z ∨ g * z * g⁻¹ = z * e}
  one_mem' := Or.inl (by group)
  mul_mem' := by
    intro a b ha hb
    have hab : a * b * z * (a * b)⁻¹ = a * (b * z * b⁻¹) * a⁻¹ := by group
    change a * b * z * (a * b)⁻¹ = z ∨ a * b * z * (a * b)⁻¹ = z * e
    rcases hb with hb | hb <;> rw [hab, hb]
    · exact ha
    · rw [hc.conj_mul_centralElt]
      rcases ha with ha | ha <;> rw [ha]
      · exact Or.inr rfl
      · exact Or.inl (hc.mul_centralElt_mul_centralElt z)
  inv_mem' := by
    intro a ha
    change a⁻¹ * z * a⁻¹⁻¹ = z ∨ a⁻¹ * z * a⁻¹⁻¹ = z * e
    rw [inv_inv]
    rcases ha with ha | ha
    · left
      calc a⁻¹ * z * a = a⁻¹ * (a * z * a⁻¹) * a := by rw [ha]
        _ = z := by group
    · right
      have h : a⁻¹ * (z * e) * a = z := by rw [← ha]; group
      calc a⁻¹ * z * a = a⁻¹ * (z * e) * a * e := by
            rw [hc.inv_conj_mul_centralElt, hc.mul_centralElt_mul_centralElt]
        _ = z * e := by rw [h]

theorem conj_eq_of_le_normalizer (hc : PartC T Q P₁ e u) {s : G} (hss : s * s = e)
    (hTs : T ≤ Subgroup.normalizer (Subgroup.zpowers s : Set G)) {t : G} (ht : t ∈ T) :
    t * s * t⁻¹ = s ∨ t * s * t⁻¹ = s * e :=
  hc.conj_eq_of_mem_zpowers hss
    ((Subgroup.mem_normalizer_iff.mp (hTs ht) s).mp (Subgroup.mem_zpowers s))

theorem mem_of_commute (hc : PartC T Q P₁ e u) {v q : G} (hvQ : v ∈ Q) (hvv : v * v = e)
    (hq : q ∈ Q) (hqv : q * v = v * q) : q = 1 ∨ q = e ∨ q = v ∨ q = v * e := by
  by_contra hne
  push Not at hne
  have hqq := hc.mul_self_of_ne hq hne.1 hne.2.1
  have h := hc.anticomm hvQ hq hvv hqq hne.2.2.1 hne.2.2.2
  rw [← hqv] at h
  exact hc.centralElt_ne_one (mul_eq_left.mp h.symm)

theorem mul_not_mem_commutator_centralizer [Finite G] (hc : PartC T Q P₁ e u)
    (hcyc : IsCyclic P₁) (S : Sylow 2 G) (hST : (S : Subgroup G) = T)
    (hnorm : T ≤ Subgroup.normalizer (Subgroup.zpowers u : Set G)) (hyT : y ∈ T)
    (hy : y ∉ Q ⊔ P₁) (hyy : y * y = e) {v : G} (hvQ : v ∈ Q) (hvv : v * v = e)
    (hTv : T ≤ Subgroup.normalizer (Subgroup.zpowers v : Set G)) {j : G} (hjQ : j ∈ Q)
    (hjv : j * v * j⁻¹ = v * e) :
    v * u ∉ ⁅Subgroup.centralizer ({v * u} : Set G), Subgroup.centralizer ({v * u} : Set G)⁆ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := Subgroup.centralizer ({v * u} : Set G) with hC
  have he := hc.commute_centralElt
  have hvu : v * u = u * v := hc.commute v hvQ u hc.self_mem
  have hzz : (v * u) * (v * u) = 1 := by
    calc v * u * (v * u) = v * (u * v) * u := by group
      _ = v * (v * u) * u := by rw [← hvu]
      _ = v * v * (u * u) := by group
      _ = 1 := by rw [hvv, hc.sq, hc.centralElt_mul_self]
  have hconj_z : ∀ t ∈ T, t * (v * u) * t⁻¹ = (v * u) ∨ t * (v * u) * t⁻¹ = (v * u) * e := by
    intro t ht
    have h1 : t * (v * u) * t⁻¹ = (t * v * t⁻¹) * (t * u * t⁻¹) := by group
    rcases hc.conj_eq_of_le_normalizer hvv hTv ht with hv | hv <;>
      rcases hc.conj_eq_of_le_normalizer hc.sq hnorm ht with hu | hu <;> rw [h1, hv, hu]
    · exact Or.inl rfl
    · exact Or.inr (by group)
    · exact Or.inr (by rw [mul_assoc v e u, ← he u]; group)
    · refine Or.inl ?_
      rw [show v * e * (u * e) = v * (e * u) * e by group, ← he u]
      calc v * (u * e) * e = v * u * (e * e) := by group
        _ = (v * u) := by rw [hc.centralElt_mul_self, mul_one]
  set N := hc.pairStabilizer (v * u) with hN
  have hTN : T ≤ N := fun t ht => hconj_z t ht
  have hCN : C ≤ N := fun g hg => Or.inl (by
    rw [Subgroup.mem_centralizer_singleton_iff] at hg
    rw [hg, mul_inv_cancel_right])
  have hjT : j ∈ T := hc.left_le hjQ
  have hju : j * u = u * j := hc.commute j hjQ u hc.self_mem
  have hjz : j * (v * u) * j⁻¹ = (v * u) * e := by
    calc j * (v * u) * j⁻¹ = (j * v * j⁻¹) * (j * u * j⁻¹) := by group
      _ = v * e * u := by rw [hjv, hju, mul_inv_cancel_right]
      _ = (v * u) * e := by rw [mul_assoc v e u, ← he u]; group
  have hnotC : ∀ g : G, g * (v * u) * g⁻¹ = (v * u) * e → g ∉ C := by
    intro g hg hgC
    rw [Subgroup.mem_centralizer_singleton_iff] at hgC
    rw [hgC, mul_inv_cancel_right] at hg
    exact hc.centralElt_ne_one (mul_eq_left.mp hg.symm)
  have hcosN : ∀ b ∈ N, b ∉ C → b * j ∈ C := by
    intro b hb hbC
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hbz : b * (v * u) * b⁻¹ = (v * u) * e := by
      rcases hb with hb | hb
      · refine absurd (Subgroup.mem_centralizer_singleton_iff.mpr ?_) hbC
        calc b * (v * u) = b * (v * u) * b⁻¹ * b := by group
          _ = v * u * b := by rw [hb]
      · exact hb
    have h : b * j * (v * u) * (b * j)⁻¹ = (v * u) := by
      calc b * j * (v * u) * (b * j)⁻¹ = b * (j * (v * u) * j⁻¹) * b⁻¹ := by group
        _ = (v * u) := by rw [hjz, hc.conj_mul_centralElt, hbz, hc.mul_centralElt_mul_centralElt]
    calc b * j * (v * u) = b * j * (v * u) * (b * j)⁻¹ * (b * j) := by group
      _ = (v * u) * (b * j) := by rw [h]
  have hCrel : C.relIndex N = 2 := relIndex_eq_two_of_mul_mem (hTN hjT) (hnotC j hjz) hcosN
  have hRrel : (T ⊓ C).relIndex T = 2 := relIndex_eq_two_of_mul_mem hjT
    (fun h => hnotC j hjz h.2) fun t ht htR =>
      ⟨T.mul_mem ht hjT, hcosN t (hTN ht) (fun h => htR ⟨ht, h⟩)⟩
  have h1 := Subgroup.relIndex_mul_relIndex (T ⊓ C) C N inf_le_right hCN
  have h2 := Subgroup.relIndex_mul_relIndex (T ⊓ C) T N inf_le_left hTN
  rw [hCrel] at h1
  rw [hRrel] at h2
  have hindex : Nat.Coprime 2 ((T ⊓ C).relIndex C) := by
    have hTi : Nat.Coprime 2 T.index := by
      rw [← hST]
      exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr S.not_dvd_index
    have heq : (T ⊓ C).relIndex C = T.relIndex N := by omega
    rw [heq]
    exact Nat.Coprime.coprime_dvd_right (Subgroup.relIndex_dvd_index_of_le hTN) hTi
  have hyv := hc.conj_eq_mul_centralElt hyT hy hyy (Subgroup.mem_sup_left hvQ) hvv
    ((Subgroup.mem_normalizer_iff.mp (hTv hyT) v).mp (Subgroup.mem_zpowers v))
  have hyu := hc.conj_eq_mul_centralElt hyT hy hyy (Subgroup.mem_sup_right hc.self_mem) hc.sq
    ((Subgroup.mem_normalizer_iff.mp (hnorm hyT) u).mp (Subgroup.mem_zpowers u))
  have hyC : y ∈ C := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h : y * (v * u) * y⁻¹ = (v * u) := by
      calc y * (v * u) * y⁻¹ = (y * v * y⁻¹) * (y * u * y⁻¹) := by group
        _ = v * e * (u * e) := by rw [hyv, hyu]
        _ = v * u * (e * e) := by rw [mul_assoc v e, ← mul_assoc e u e, ← he u]; group
        _ = v * u := by rw [hc.centralElt_mul_self, mul_one]
    calc y * (v * u) = y * (v * u) * y⁻¹ * y := by group
      _ = (v * u) * y := by rw [h]
  have hP₁C : P₁ ≤ C := fun p hp => by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hpv := hc.commute v hvQ p hp
    have hpu := comm_right_of_isCyclic hcyc hp hc.self_mem
    calc p * (v * u) = p * v * u := by group
      _ = v * p * u := by rw [hpv]
      _ = v * (p * u) := by group
      _ = v * u * p := by rw [hpu]; group
  have hPC : P₁ ⊔ Subgroup.zpowers y ≤ C := _root_.sup_le hP₁C (Subgroup.zpowers_le.mpr hyC)
  have hzT : (v * u) ∈ T := T.mul_mem (hc.left_le hvQ) (hc.right_le hc.self_mem)
  have hzC : (v * u) ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have heP : e ∈ P₁ ⊔ Subgroup.zpowers y := Subgroup.mem_sup_left hc.mem_right
  have huP : u ∈ P₁ ⊔ Subgroup.zpowers y := Subgroup.mem_sup_left hc.self_mem
  have hzP : (v * u) ∉ P₁ ⊔ Subgroup.zpowers y := by
    intro hzP
    have hvP : v ∈ P₁ ⊔ Subgroup.zpowers y := by
      rw [show v = v * u * u⁻¹ by group]
      exact Subgroup.mul_mem _ hzP (Subgroup.inv_mem _ huP)
    rcases hc.mem_inf_sup_zpowers hyT hy (hyy ▸ hc.mem_right) hvQ hvP with h | h
    · exact (hc.ne_of_mul_self_eq hvv).1 h
    · exact (hc.ne_of_mul_self_eq hvv).2 h
  have hcosR : ∀ t ∈ T ⊓ C, t ∉ P₁ ⊔ Subgroup.zpowers y →
      t * (v * u) ∈ P₁ ⊔ Subgroup.zpowers y := by
    rintro t ⟨htT, htC⟩ htP
    obtain ⟨q, hq, w, hw, rfl⟩ := hc.exists_mul_eq_of_mem hyT hy htT
    have hwz : w * (v * u) = (v * u) * w := Subgroup.mem_centralizer_singleton_iff.mp (hPC hw)
    have hqz : q * (v * u) = (v * u) * q := by
      have h := Subgroup.mem_centralizer_singleton_iff.mp htC
      have h' : q * (v * u) * w = (v * u) * q * w := by
        calc q * (v * u) * w = q * ((v * u) * w) := by group
          _ = q * (w * (v * u)) := by rw [hwz]
          _ = (v * u) * (q * w) := by rw [← mul_assoc, h]
          _ = (v * u) * q * w := by group
      exact mul_right_cancel h'
    have hqv : q * v = v * q := by
      have hqu := hc.commute q hq u hc.self_mem
      have h' : q * v * u = v * q * u := by
        calc q * v * u = q * (v * u) := by group
          _ = (v * u) * q := hqz
          _ = v * (u * q) := by group
          _ = v * q * u := by rw [← hqu]; group
      exact mul_right_cancel h'
    rcases hc.mem_of_commute hvQ hvv hq hqv with h | h | h | h <;> rw [h] at htP ⊢
    · exact absurd (by rw [one_mul]; exact hw) htP
    · exact absurd (Subgroup.mul_mem _ heP hw) htP
    · have h' : v * w * (v * u) = e * u * w := by
        calc v * w * (v * u) = v * ((v * u) * w) := by rw [mul_assoc, hwz]
          _ = v * v * u * w := by group
          _ = e * u * w := by rw [hvv]
      rw [h']
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ heP huP) hw
    · have h' : v * e * w * (v * u) = u * w := by
        calc v * e * w * (v * u) = v * e * ((v * u) * w) := by rw [mul_assoc, hwz]
          _ = v * (e * v) * u * w := by group
          _ = v * v * e * u * w := by rw [← he v]; group
          _ = u * w := by rw [hvv, hc.centralElt_mul_self, one_mul]
      rw [h']
      exact Subgroup.mul_mem _ huP hw
  exact not_mem_commutator_of_central inf_le_right hindex (le_inf (hc.sup_zpowers_le hyT) hPC)
    (relIndex_eq_two_of_mul_mem ⟨hzT, hzC⟩ hzP hcosR) ⟨hzT, hzC⟩ hzP hzz
    fun g hg => Subgroup.mem_centralizer_singleton_iff.mp hg

end PartC

end CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore
