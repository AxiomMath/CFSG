module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreC3Top

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

open QuaternionGroup

variable {G : Type} [Group G] {T Q P₁ S : Subgroup G} {e u y x : G}

namespace CaseC3

@[expose] def Genuine (Z : Subgroup G) [Z.Normal] (a : G ⧸ Z) : Prop :=
  ∃ g : G, (g : G ⧸ Z) = a ∧ g * g = 1

variable (Z : Subgroup G) [Z.Normal]

theorem genuine_conj {a : G ⧸ Z} (ha : Genuine Z a) (b : G ⧸ Z) : Genuine Z (b⁻¹ * a * b) := by
  obtain ⟨g, rfl, hg⟩ := ha
  obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective b
  refine ⟨c⁻¹ * g * c, by simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv], ?_⟩
  rw [show c⁻¹ * g * c * (c⁻¹ * g * c) = c⁻¹ * (g * g) * c by group, hg]
  group

theorem mem_of_genuine (h : CaseC3 T Q P₁ e u y) (hZ : ∀ x, x ∈ Z ↔ x = 1 ∨ x = e)
    {a : G ⧸ Z} (haT : a ∈ T.map (QuotientGroup.mk' Z)) (ha : Genuine Z a) (ha1 : a ≠ 1) :
    a ∈ (Q ⊔ P₁).map (QuotientGroup.mk' Z) := by
  have hc := h.partC
  have hZW := hc.le_sup_of_mem_iff Z hZ
  obtain ⟨g, rfl, hg⟩ := ha
  rw [PartC.mk_mem_map_iff_of_le Z (hZW.trans hc.sup_le)] at haT
  rw [PartC.mk_mem_map_iff_of_le Z hZW]
  have hg1 : g ≠ 1 := fun h1 => ha1 (by rw [h1, QuotientGroup.mk_one])
  exact hc.involution_mem g haT (orderOf_eq_prime (by rw [pow_two]; exact hg) hg1)

theorem conj_moved (h : CaseC3 T Q P₁ e u y) {m : G} (hm : m ∈ P₁)
    (hm1 : y * m * y⁻¹ ≠ m) (hm2 : y * m * y⁻¹ ≠ m * e) :
    y * m * y⁻¹ = u * m ∨ y * m * y⁻¹ = u * m * e := by
  have hc := h.partC
  obtain ⟨φ⟩ := h.quaternion_right
  have heP := hc.mem_right
  have he2 := hc.order
  have hfix : ∀ w : G, (w = 1 ∨ w = e ∨ w = u ∨ w = u * e) →
      y * w * y⁻¹ = w ∨ y * w * y⁻¹ = w * e := by
    rintro w (rfl | rfl | rfl | rfl)
    · left
      group
    · exact Or.inl (hc.conj_centralElt y)
    · exact h.conj_self
    · exact conj_mul_mod_central hc.center hc.centralElt_mul_self h.conj_self
        (Or.inl (hc.conj_centralElt y))
  have hmU : ¬ (m = 1 ∨ m = e ∨ m = u ∨ m = u * e) := fun h' => by
    rcases hfix m h' with h1 | h1
    exacts [hm1 h1, hm2 h1]
  push Not at hmU
  have hmm := quaternion_mul_self_of_ne φ heP he2 hm hmU.1 hmU.2.1
  have hb := hc.normal_right y h.mem m hm
  have hy' : y⁻¹ ∈ T := T.inv_mem h.mem
  have hinj : ∀ a c : G, y * a * y⁻¹ = y * c * y⁻¹ → a = c := fun a c h' =>
    mul_left_cancel (mul_right_cancel h')
  rcases quaternion_enum φ heP he2 hc.self_mem hm hb hc.sq hmm hmU.2.2.1 hmU.2.2.2 with
    h1 | h1 | h1 | h1 | h1 | h1 | h1 | h1
  · exfalso
    rw [mul_inv_eq_one, mul_eq_left] at h1
    exact hmU.1 h1
  · exfalso
    rw [← hc.conj_centralElt y] at h1
    exact hmU.2.1 (hinj _ _ h1)
  · exfalso
    have hm' : m = y⁻¹ * u * y⁻¹⁻¹ := by rw [← h1]; group
    rcases h.conj_self_of_mem hy' with h2 | h2 <;> rw [h2] at hm'
    exacts [hmU.2.2.1 hm', hmU.2.2.2 hm']
  · exfalso
    have hm' : m = y⁻¹ * u * y⁻¹⁻¹ * e := by
      rw [show y⁻¹ * u * y⁻¹⁻¹ * e = y⁻¹ * (u * e) * y⁻¹⁻¹ by
        rw [show y⁻¹ * (u * e) * y⁻¹⁻¹ = y⁻¹ * u * (e * y⁻¹⁻¹) by group,
          ← hc.commute_centralElt y⁻¹⁻¹, ← mul_assoc], ← h1]
      group
    rcases h.conj_self_of_mem hy' with h2 | h2 <;> rw [h2] at hm'
    · exact hmU.2.2.2 hm'
    · exact hmU.2.2.1 (by rw [hm', hc.mul_centralElt_mul_centralElt])
  · exact absurd h1 hm1
  · exact absurd h1 hm2
  · exact Or.inl h1
  · exact Or.inr h1

end CaseC3

theorem caseC3_rearrange {H : Type*} [Group H] {M N U V : H} (hMU : Commute M U)
    (hNU : Commute N U) (hNV : Commute N V) (hMN : Commute M N) (hM : M * M = 1)
    (hN : N * N = 1) : M * N * (U * M) * (V * N) = U * V := by
  calc M * N * (U * M) * (V * N) = M * (N * U) * M * V * N := by group
    _ = M * (U * N) * M * V * N := by rw [hNU.eq]
    _ = (M * U) * (N * M) * V * N := by group
    _ = (U * M) * (M * N) * V * N := by rw [hMU.eq, hMN.symm.eq]
    _ = U * (M * M) * (N * V) * N := by group
    _ = U * (V * N) * N := by rw [hM, hNV.eq]; group
    _ = U * V := by rw [mul_assoc, mul_assoc, hN, mul_one]

theorem caseC3_pow_four_identity {H : Type*} [Group H] {M X N Yb U V : H}
    (hXM : X * M * X⁻¹ = N) (hC : X * X * (M * N) * (X * X)⁻¹ = Yb * (M * N) * Yb⁻¹)
    (hτM : Yb * M * Yb⁻¹ = U * M) (hτN : Yb * N * Yb⁻¹ = V * N) (hMU : Commute M U)
    (hNU : Commute N U) (hNV : Commute N V) (hMN : Commute M N) (hM : M * M = 1)
    (hN : N * N = 1) : (M * X) ^ 4 = U * V * X ^ 4 := by
  calc (M * X) ^ 4 = (M * X * (M * X)) * (M * X * (M * X)) := by
        rw [show (4 : ℕ) = 2 + 2 by norm_num, pow_add, pow_two]
    _ = (M * N) * (X * X * (M * N) * (X * X)⁻¹) * (X * X * (X * X)) := by rw [← hXM]; group
    _ = (M * N) * (Yb * (M * N) * Yb⁻¹) * (X * X * (X * X)) := by rw [hC]
    _ = (M * N) * ((Yb * M * Yb⁻¹) * (Yb * N * Yb⁻¹)) * (X * X * (X * X)) := by group
    _ = M * N * (U * M) * (V * N) * (X * X * (X * X)) := by rw [hτM, hτN]; group
    _ = U * V * (X * X * (X * X)) := by rw [caseC3_rearrange hMU hNU hNV hMN hM hN]
    _ = U * V * X ^ 4 := by rw [show (4 : ℕ) = 2 + 2 by norm_num, pow_add, pow_two]

namespace CaseC3

variable (Z : Subgroup G) [Z.Normal]

theorem mk_mul_ne_one (h : CaseC3 T Q P₁ e u y) (hZ : ∀ x, x ∈ Z ↔ x = 1 ∨ x = e) {v : G}
    (hvQ : v ∈ Q) (hvv : v * v = e) : (u : G ⧸ Z) * (v : G ⧸ Z) ≠ 1 := by
  have hc := h.partC
  intro h1
  rw [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff, hZ] at h1
  have hvP : v ∈ P₁ := by
    rcases h1 with h1 | h1
    · rw [eq_inv_of_mul_eq_one_right h1]
      exact P₁.inv_mem hc.self_mem
    · rw [show v = u⁻¹ * e by rw [← h1]; group]
      exact P₁.mul_mem (P₁.inv_mem hc.self_mem) hc.mem_right
  rcases hc.mem_inf v hvQ hvP with h2 | h2
  · exact hc.centralElt_ne_one (by rw [← hvv, h2, mul_one])
  · exact hc.centralElt_ne_one (by rw [← hvv, h2, hc.centralElt_mul_self])

theorem genuine_mul (h : CaseC3 T Q P₁ e u y) {v : G} (hvQ : v ∈ Q) (hvv : v * v = e) :
    Genuine Z ((u : G ⧸ Z) * (v : G ⧸ Z)) := by
  have hc := h.partC
  refine ⟨u * v, QuotientGroup.mk_mul Z u v, ?_⟩
  rw [show u * v * (u * v) = u * (v * u) * v by group, hc.commute v hvQ u hc.self_mem,
    show u * (u * v) * v = u * u * (v * v) by group, hc.sq, hvv, hc.centralElt_mul_self]

end CaseC3

namespace CaseC3Top

variable [Finite G] (Z : Subgroup G) [Z.Normal]

omit [Finite G] in
theorem mul_mem_of_not_mem (hs : CaseC3Top T Q P₁ S e u y x) {s s' : G} (hsS : s ∈ S)
    (hsT : s ∉ T) (hs'S : s' ∈ S) (hs'T : s' ∉ T) : s * s' ∈ T := by
  have h1 := hs.mul_inv_mem hsS hsT
  have h2 := hs.mul_inv_mem hs'S hs'T
  have hxt : x * (s' * x⁻¹) * x⁻¹ ∈ T :=
    (Subgroup.mem_normalizer_iff.mp hs.mem_normalizer _).mp h2
  rw [show s * s' = (s * x⁻¹) * (x * (s' * x⁻¹) * x⁻¹) * (x * x) by group]
  exact T.mul_mem (T.mul_mem h1 hxt) hs.mul_self_mem

theorem mul_self_not_mem_of_typeA (hs : CaseC3Top T Q P₁ S e u y x) (hA : x * x ∉ Q ⊔ P₁)
    {s : G} (hsS : s ∈ S) (hsT : s ∉ T) : s * s ∉ Q ⊔ P₁ := fun h' => hA (by
  have h1 := hs.mul_self_mem_mul hsS hsT
  rw [show x * x = (s * s * (x * x)⁻¹)⁻¹ * (s * s) by
    rw [eq_inv_mul_iff_mul_eq, inv_mul_cancel_right]]
  exact (Q ⊔ P₁).mul_mem ((Q ⊔ P₁).inv_mem h1) h')

theorem mk_pow_four (hs : CaseC3Top T Q P₁ S e u y x) (hZ : ∀ x, x ∈ Z ↔ x = 1 ∨ x = e)
    (hA : x * x ∉ Q ⊔ P₁) {v : G} (hvQ : v ∈ Q) (hvv : v * v = e) (hyv : y * v * y⁻¹ = v⁻¹)
    (hvfix : ∀ w ∈ Q, (y * w * y⁻¹ = w ∨ y * w * y⁻¹ = w * e) →
      w = 1 ∨ w = e ∨ w = v ∨ w = v * e) {s : G} (hsS : s ∈ S) (hsT : s ∉ T) :
    (s : G ⧸ Z) ^ 4 = 1 ∨ (s : G ⧸ Z) ^ 4 = (u : G ⧸ Z) * (v : G ⧸ Z) := by
  have hc := hs.partC
  have ht := hs.mul_mem_of_not_mem hsS hsT hsS hsT
  have htW := hs.mul_self_not_mem_of_typeA hA hsS hsT
  have h4 : (s : G ⧸ Z) ^ 4 = ((s * s * (s * s) : G) : G ⧸ Z) := by
    rw [show (4 : ℕ) = 2 + 2 by norm_num, pow_add, pow_two, QuotientGroup.mk_mul,
      QuotientGroup.mk_mul]
  have hmem : ((s * s * (s * s) : G) : G ⧸ Z) ∈ (Q ⊔ P₁).map (QuotientGroup.mk' Z) ⊓
      Subgroup.centralizer {((s * s : G) : G ⧸ Z)} :=
    ⟨Subgroup.mem_map_of_mem _ (hc.mul_self_mem_sup ht),
      Subgroup.mem_centralizer_singleton_iff.mpr (by
        simp only [QuotientGroup.mk_mul]
        group)⟩
  have hcomm : ((s * s * (s * s) : G) : G ⧸ Z) * (s : G ⧸ Z) =
      (s : G ⧸ Z) * ((s * s * (s * s) : G) : G ⧸ Z) := by
    simp only [QuotientGroup.mk_mul]
    group
  have hZP : Z ≤ P₁ := fun g hg => by
    rcases (hZ g).mp hg with rfl | rfl
    exacts [P₁.one_mem, hc.mem_right]
  have hZQ : Z ≤ Q := fun g hg => by
    rcases (hZ g).mp hg with rfl | rfl
    exacts [Q.one_mem, hc.mem_left]
  obtain ⟨hsP, hsQ⟩ := hs.swap hsS hsT
  rw [h4]
  rcases (hs.toCaseC3.mem_map_sup_inf_centralizer_iff Z hZ hvQ hvv hyv hvfix _).mp
      (hs.toCaseC3.map_sup_inf_centralizer_le Z hZ ht htW hmem) with h1 | h1 | h1 | h1
  · exact Or.inl h1
  · left
    rw [h1] at hcomm ⊢
    exact hc.mk_eq_one_of_commute Z hZ hZP (fun g hg hg' => hc.mem_inf g hg' hg) hc.self_mem
      (hsP u hc.self_mem) hcomm
  · left
    rw [h1] at hcomm ⊢
    exact hc.mk_eq_one_of_commute Z hZ hZQ hc.mem_inf hvQ (hsQ v hvQ) hcomm
  · exact Or.inr h1

theorem mk_mul_pow_four (hs : CaseC3Top T Q P₁ S e u y x) (hZ : ∀ x, x ∈ Z ↔ x = 1 ∨ x = e)
    (hA : x * x ∉ Q ⊔ P₁) {v : G} (hvQ : v ∈ Q)
    (hvfix : ∀ w ∈ Q, (y * w * y⁻¹ = w ∨ y * w * y⁻¹ = w * e) →
      w = 1 ∨ w = e ∨ w = v ∨ w = v * e) {m : G} (hm : m ∈ P₁)
    (hm1 : y * m * y⁻¹ ≠ m) (hm2 : y * m * y⁻¹ ≠ m * e) :
    ((m : G ⧸ Z) * (x : G ⧸ Z)) ^ 4 = (u : G ⧸ Z) * (v : G ⧸ Z) * (x : G ⧸ Z) ^ 4 := by
  have hc := hs.partC
  obtain ⟨φ⟩ := hs.quaternion_right
  have he1 : ((e : G) : G ⧸ Z) = 1 := (QuotientGroup.eq_one_iff e).mpr ((hZ e).mpr (Or.inr rfl))
  have hmW : m ∈ Q ⊔ P₁ := Subgroup.mem_sup_right hm
  have hnW : x * m * x⁻¹ ∈ Q ⊔ P₁ := hs.conj_mem_sup hmW
  have hXM : (x : G ⧸ Z) * (m : G ⧸ Z) * (x : G ⧸ Z)⁻¹ = ((x * m * x⁻¹ : G) : G ⧸ Z) := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
  have hτM : (y : G ⧸ Z) * (m : G ⧸ Z) * (y : G ⧸ Z)⁻¹ = (u : G ⧸ Z) * (m : G ⧸ Z) := by
    rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    rcases hs.toCaseC3.conj_moved hm hm1 hm2 with h1 | h1 <;> rw [h1]
    · rw [QuotientGroup.mk_mul]
    · rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, he1, mul_one]
  have hσU : (x : G ⧸ Z) * (u : G ⧸ Z) * (x : G ⧸ Z)⁻¹ = (v : G ⧸ Z) := by
    rw [← hs.mk_conj_self Z hZ hvfix, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
      QuotientGroup.mk_inv]
  have hτN : (y : G ⧸ Z) * ((x * m * x⁻¹ : G) : G ⧸ Z) * (y : G ⧸ Z)⁻¹ =
      (v : G ⧸ Z) * ((x * m * x⁻¹ : G) : G ⧸ Z) := by
    have h1 := hs.mk_conj_conj_comm Z hZ hmW
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv] at h1 ⊢
    rw [← h1, hτM, ← hσU]
    group
  have hC : (x : G ⧸ Z) * (x : G ⧸ Z) * ((m : G ⧸ Z) * ((x * m * x⁻¹ : G) : G ⧸ Z)) *
      ((x : G ⧸ Z) * (x : G ⧸ Z))⁻¹ =
      (y : G ⧸ Z) * ((m : G ⧸ Z) * ((x * m * x⁻¹ : G) : G ⧸ Z)) * (y : G ⧸ Z)⁻¹ := by
    have h1 := hs.toCaseC3.mk_conj_eq_of_not_mem Z hZ hs.mul_self_mem hA
      ((Q ⊔ P₁).mul_mem hmW hnW)
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv] at h1 ⊢
    exact h1
  have hWM : (m : G ⧸ Z) ∈ (Q ⊔ P₁).map (QuotientGroup.mk' Z) := Subgroup.mem_map_of_mem _ hmW
  have hWN : ((x * m * x⁻¹ : G) : G ⧸ Z) ∈ (Q ⊔ P₁).map (QuotientGroup.mk' Z) :=
    Subgroup.mem_map_of_mem _ hnW
  have hWU : (u : G ⧸ Z) ∈ (Q ⊔ P₁).map (QuotientGroup.mk' Z) :=
    Subgroup.mem_map_of_mem _ (Subgroup.mem_sup_right hc.self_mem)
  have hWV : (v : G ⧸ Z) ∈ (Q ⊔ P₁).map (QuotientGroup.mk' Z) :=
    Subgroup.mem_map_of_mem _ (Subgroup.mem_sup_left hvQ)
  have hcm := fun {a b : G ⧸ Z} (ha : a ∈ (Q ⊔ P₁).map (QuotientGroup.mk' Z))
      (hb : b ∈ (Q ⊔ P₁).map (QuotientGroup.mk' Z)) =>
    (hc.mul_comm_of_mem_map_sup Z φ hZ ha hb : Commute a b)
  have hsq := fun {a : G ⧸ Z} (ha : a ∈ (Q ⊔ P₁).map (QuotientGroup.mk' Z)) => by
    have := hc.pow_two_eq_one_of_mem_map_sup Z φ hZ ha
    rwa [pow_two] at this
  exact caseC3_pow_four_identity hXM hC hτM hτN (hcm hWM hWU) (hcm hWN hWU) (hcm hWN hWV)
    (hcm hWM hWN) (hsq hWM) (hsq hWN)

end CaseC3Top

end CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore
