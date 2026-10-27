module

public import CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree.Families
public import CFSG.RankThree.PartOne.CTP.AltGen

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank

open Equiv Equiv.Perm CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree

theorem exists_conj_embedding_alt {K : Type*} [Group K] (Ls : Subgroup K) [Ls.Normal] (n : ℕ)
    (hn : 5 ≤ n) (hn6 : n ≠ 6) (φ : ↥Ls ≃* alternatingGroup (Fin n)) :
    ∃ e : K →* Perm (Fin n),
      (∀ x : ↥Ls, e (x : K) = (φ x : Perm (Fin n))) ∧
      (∀ (g : K) (x : ↥Ls), (φ (MulAut.conjNormal g x) : Perm (Fin n)) =
        e g * (φ x : Perm (Fin n)) * (e g)⁻¹) ∧
      (∀ g : K, e g = 1 → ∀ x : ↥Ls, g * (x : K) * g⁻¹ = (x : K)) ∧
      (∀ g : K, (∀ x : ↥Ls, g * (x : K) * g⁻¹ = (x : K)) → e g = 1) := by
  have hbij := CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj n hn hn6
  let cEquiv : Perm (Fin n) ≃* MulAut (alternatingGroup (Fin n)) := MulEquiv.ofBijective _ hbij
  let ec : K →* MulAut (alternatingGroup (Fin n)) :=
    (MulAut.congr φ).toMonoidHom.comp (MulAut.conjNormal (H := Ls))
  let e : K →* Perm (Fin n) := cEquiv.symm.toMonoidHom.comp ec
  have hce : ∀ g : K, MulAut.conjNormal (e g) = ec g := fun g => by
    show cEquiv (cEquiv.symm (ec g)) = ec g
    exact cEquiv.apply_symm_apply _
  have hconj : ∀ (g : K) (x : ↥Ls),
      (φ (MulAut.conjNormal g x) : Perm (Fin n)) = e g * (φ x : Perm (Fin n)) * (e g)⁻¹ := by
    intro g x
    have h1 := congrArg (fun f : MulAut (alternatingGroup (Fin n)) =>
      ((f (φ x) : alternatingGroup (Fin n)) : Perm (Fin n))) (hce g)
    simp only [MulAut.conjNormal_apply] at h1
    rw [h1]
    simp [ec, MulAut.congr_apply]
  have hL : ∀ x : ↥Ls, e (x : K) = (φ x : Perm (Fin n)) := by
    intro x
    apply hbij.1
    rw [hce]
    ext a
    obtain ⟨y, rfl⟩ := φ.surjective a
    have h1 : (ec (x : K)) (φ y) = φ (MulAut.conjNormal (x : K) y) := by
      simp [ec, MulAut.congr_apply]
    rw [h1]
    have e1 : MulAut.conjNormal (x : K) y = x * y * x⁻¹ := by
      apply Subtype.ext
      simp
    rw [e1, map_mul, map_mul, map_inv]
    simp
  refine ⟨e, hL, hconj, ?_, ?_⟩
  · intro g hg x
    have h1 := hconj g x
    rw [hg] at h1
    simp only [one_mul, inv_one, mul_one] at h1
    have h2 : MulAut.conjNormal g x = x := φ.injective (Subtype.ext h1)
    have h3 := congrArg Subtype.val h2
    simpa using h3
  · intro g hg
    have h1 : (MulAut.conjNormal (H := Ls) g) = 1 := by
      ext x
      simp [hg x]
    have h2 : ec g = 1 := by
      show (MulAut.congr φ) (MulAut.conjNormal (H := Ls) g) = 1
      rw [h1]
      exact map_one _
    show cEquiv.symm (ec g) = 1
    rw [h2, map_one]


section Helpers

theorem mem_sup_of_commute' {X : Type*} [Group X] {A B : Subgroup X}
    (h : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {x : X} (hx : x ∈ A ⊔ B) :
    ∃ a ∈ A, ∃ b ∈ B, x = a * b := by
  rw [Subgroup.sup_eq_closure] at hx
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    rcases hy with hy | hy
    · exact ⟨y, hy, 1, B.one_mem, (mul_one y).symm⟩
    · exact ⟨1, A.one_mem, y, hy, (one_mul y).symm⟩
  | one => exact ⟨1, A.one_mem, 1, B.one_mem, (mul_one 1).symm⟩
  | mul x y _ _ hx hy =>
    obtain ⟨a1, ha1, b1, hb1, rfl⟩ := hx
    obtain ⟨a2, ha2, b2, hb2, rfl⟩ := hy
    refine ⟨a1 * a2, A.mul_mem ha1 ha2, b1 * b2, B.mul_mem hb1 hb2, ?_⟩
    have := h a2 ha2 b1 hb1
    calc a1 * b1 * (a2 * b2) = a1 * (b1 * a2) * b2 := by group
      _ = a1 * (a2 * b1) * b2 := by rw [this]
      _ = a1 * a2 * (b1 * b2) := by group
  | inv x _ hx =>
    obtain ⟨a, ha, b, hb, rfl⟩ := hx
    refine ⟨a⁻¹, A.inv_mem ha, b⁻¹, B.inv_mem hb, ?_⟩
    have := h a ha b hb
    rw [mul_inv_rev]
    exact (Commute.inv_inv (this : a * b = b * a)).eq.symm

theorem isThreeCycle_swap_mul_swap_of_ne {V : Type*} [DecidableEq V] [Fintype V] {x y z : V}
    (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z) : (swap x y * swap y z).IsThreeCycle := by
  have hnd : [x, y, z].Nodup := by simp [hxy, hyz, hxz]
  rw [← card_support_eq_three_iff, Equiv.Perm.support_swap_mul_swap hnd]
  simp [hxy, hyz, hxz]

theorem one_le_pRank_zpowers {G : Type*} [Group G] [Finite G] {r : G} (hr : orderOf r = 3) :
    1 ≤ CFSG.Open.pRank 3 (Subgroup.zpowers r) := by
  unfold CFSG.Open.pRank
  have hcard : Nat.card (Subgroup.zpowers r) = 3 ^ 1 := by
    rw [Nat.card_zpowers, hr]; norm_num
  refine le_csSup ⟨Nat.card G, ?_⟩ ⟨Subgroup.zpowers r, le_rfl, ⟨inferInstance, ?_⟩, hcard⟩
  · rintro k ⟨B, -, -, hB⟩
    calc k ≤ 3 ^ k := (Nat.lt_pow_self (by norm_num)).le
      _ = Nat.card B := hB.symm
      _ ≤ Nat.card G := Subgroup.card_le_card_group B
  · intro x hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    have : (r ^ k) ^ 3 = (r ^ 3) ^ k := by
      rw [← zpow_natCast, ← zpow_natCast r 3, ← zpow_mul, ← zpow_mul, mul_comm]
    rw [this, ← hr, pow_orderOf_eq_one, one_zpow]

theorem mem_normalizer_zpowers {X : Type*} [Group X] {y r : X}
    (h1 : y * r * y⁻¹ ∈ Subgroup.zpowers r) (h2 : y⁻¹ * r * y ∈ Subgroup.zpowers r) :
    y ∈ Subgroup.normalizer ((Subgroup.zpowers r : Subgroup X) : Set X) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
    have : y * r ^ k * y⁻¹ = (y * r * y⁻¹) ^ k := (conj_zpow).symm
    rw [this]
    exact Subgroup.zpow_mem _ h1 k
  · intro hh
    have : h = (y⁻¹ * (y * h * y⁻¹) * y) := by group
    rw [this]
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hh
    have e : y⁻¹ * (y * h * y⁻¹) * y = (y⁻¹ * r * y) ^ k := by
      rw [← hk]
      simpa using (conj_zpow (a := y⁻¹) (b := r) (i := k)).symm
    rw [e]
    exact Subgroup.zpow_mem _ h2 k

end Helpers


section Main

theorem exists_disjoint_threeCycles (n : ℕ) (hn : 6 ≤ n) :
    ∃ a b : Perm (Fin n), a.IsThreeCycle ∧ b.IsThreeCycle ∧ Disjoint a.support b.support := by
  classical
  let p : ℕ → Fin n := fun i => if h : i < n then ⟨i, h⟩ else ⟨0, by omega⟩
  have hp : ∀ i, i < n → (p i : ℕ) = i := fun i hi => by simp [p, hi]
  have hne : ∀ i j, i < 6 → j < 6 → i ≠ j → p i ≠ p j := by
    intro i j hi hj hij h
    have := congrArg (fun z : Fin n => (z : ℕ)) h
    simp only [hp i (by omega), hp j (by omega)] at this
    exact hij this
  have h01 := hne 0 1 (by norm_num) (by norm_num) (by norm_num)
  have h12 := hne 1 2 (by norm_num) (by norm_num) (by norm_num)
  have h02 := hne 0 2 (by norm_num) (by norm_num) (by norm_num)
  have h34 := hne 3 4 (by norm_num) (by norm_num) (by norm_num)
  have h45 := hne 4 5 (by norm_num) (by norm_num) (by norm_num)
  have h35 := hne 3 5 (by norm_num) (by norm_num) (by norm_num)
  refine ⟨swap (p 0) (p 1) * swap (p 1) (p 2), swap (p 3) (p 4) * swap (p 4) (p 5),
    isThreeCycle_swap_mul_swap_of_ne h01 h12 h02, isThreeCycle_swap_mul_swap_of_ne h34 h45 h35, ?_⟩
  have hnd1 : [p 0, p 1, p 2].Nodup := by simp [h01, h12, h02]
  have hnd2 : [p 3, p 4, p 5].Nodup := by simp [h34, h45, h35]
  rw [Equiv.Perm.support_swap_mul_swap hnd1, Equiv.Perm.support_swap_mul_swap hnd2,
    Finset.disjoint_left]
  intro v hv hv'
  simp only [Finset.mem_insert, Finset.mem_singleton] at hv hv'
  rcases hv with rfl | rfl | rfl <;> rcases hv' with h | h | h <;>
    exact hne _ _ (by norm_num) (by norm_num) (by norm_num) h

theorem exists_conj_two_mem_sylow {X : Type*} [Group X] [Finite X] (P : Sylow 3 X) {q1 q2 : X}
    (h1 : orderOf q1 = 3) (h2 : orderOf q2 = 3) (hc : q1 * q2 = q2 * q1) :
    ∃ g : X, g * q1 * g⁻¹ ∈ (P : Subgroup X) ∧ g * q2 * g⁻¹ ∈ (P : Subgroup X) := by
  have hcomm : ∀ a ∈ Subgroup.zpowers q1, ∀ b ∈ Subgroup.zpowers q2, a * b = b * a := by
    intro a ha b hb
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    exact (Commute.zpow_zpow (show Commute q1 q2 from hc) i j).eq
  have hQ : IsPGroup 3 ↥(Subgroup.zpowers q1 ⊔ Subgroup.zpowers q2) := by
    rw [IsPGroup.iff_orderOf]
    rintro ⟨g, hg⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_sup_of_commute' hcomm hg
    have hab : Commute a b := hcomm a ha b hb
    have h3 : (a * b) ^ 3 = 1 := by
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
      rw [hab.mul_pow]
      have e1 : (q1 ^ i) ^ 3 = 1 := by
        rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← h1,
          pow_orderOf_eq_one, one_zpow]
      have e2 : (q2 ^ j) ^ 3 = 1 := by
        rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← h2,
          pow_orderOf_eq_one, one_zpow]
      rw [e1, e2, one_mul]
    have hd : orderOf (a * b) ∣ 3 := orderOf_dvd_of_pow_eq_one h3
    rw [Subgroup.orderOf_mk]
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp hd with h | h
    · exact ⟨0, by simpa using h⟩
    · exact ⟨1, by simpa using h⟩
  obtain ⟨P1, hP1⟩ := hQ.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X P1 P
  have hmem : ∀ q ∈ (P1 : Subgroup X), g * q * g⁻¹ ∈ (P : Subgroup X) := by
    intro q hq
    have h := Sylow.coe_smul (g := g) (P := P1)
    have hm : (MulAut.conj g) q ∈ ((g • P1 : Sylow 3 X) : Set X) := by
      rw [h]; exact Set.smul_mem_smul_set hq
    rw [hg] at hm
    have hm' : g * q * g⁻¹ ∈ P := by simpa [MulAut.conj_apply] using hm
    exact hm'
  refine ⟨g, hmem _ (hP1 ?_), hmem _ (hP1 ?_)⟩
  · exact Subgroup.mem_sup_left (Subgroup.mem_zpowers q1)
  · exact Subgroup.mem_sup_right (Subgroup.mem_zpowers q2)

theorem gammaCore_eq_top_of_alt {X : Type} [Group X] [Finite X] {K : Subgroup X} [K.Normal]
    {n : ℕ} (hn : 7 ≤ n) (φ : ↥K ≃* alternatingGroup (Fin n))
    (hC : Subgroup.centralizer (K : Set X) = ⊥) (P : Sylow 3 X) :
    gammaCore 3 1 ⊤ (P : Subgroup X) = ⊤ := by
  classical
  have hn5 : 5 ≤ n := by omega
  have hn6 : n ≠ 6 := by omega
  obtain ⟨e, hKe, -, hker, -⟩ := exists_conj_embedding_alt K n hn5 hn6 φ
  have hinj : Function.Injective e := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have hg' : g ∈ Subgroup.centralizer (K : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      have := hker g hg ⟨h, hh⟩
      exact (mul_inv_eq_iff_eq_mul.mp this).symm
    rw [hC] at hg'
    exact Subgroup.mem_bot.mp hg'
  have hrange : ∀ σ ∈ alternatingGroup (Fin n), ∃ x : X, e x = σ := fun σ hσ =>
    ⟨(φ.symm ⟨σ, hσ⟩ : K), by rw [hKe]; simp⟩
  obtain ⟨a0, b0, ha0, hb0, hab0⟩ := exists_disjoint_threeCycles n (by omega)
  obtain ⟨q1, hq1⟩ := hrange a0 ha0.mem_alternatingGroup
  obtain ⟨q2, hq2⟩ := hrange b0 hb0.mem_alternatingGroup
  have hq1o : orderOf q1 = 3 := by
    rw [← orderOf_injective e hinj q1, hq1]; exact ha0.orderOf
  have hq2o : orderOf q2 = 3 := by
    rw [← orderOf_injective e hinj q2, hq2]; exact hb0.orderOf
  have hq12 : q1 * q2 = q2 * q1 := by
    apply hinj
    rw [map_mul, map_mul, hq1, hq2]
    exact (Equiv.Perm.Disjoint.commute (disjoint_iff_disjoint_support.mpr hab0)).eq
  obtain ⟨g, hg1, hg2⟩ := exists_conj_two_mem_sylow P hq1o hq2o hq12
  set r1 : X := g * q1 * g⁻¹ with hr1
  set r2 : X := g * q2 * g⁻¹ with hr2
  set σ : Perm (Fin n) := e g with hσ
  set a' : Perm (Fin n) := σ * a0 * σ⁻¹ with ha'
  set b' : Perm (Fin n) := σ * b0 * σ⁻¹ with hb'
  have he1 : e r1 = a' := by rw [hr1, map_mul, map_mul, hq1, map_inv]
  have he2 : e r2 = b' := by rw [hr2, map_mul, map_mul, hq2, map_inv]
  have ha'3 : a'.IsThreeCycle := by
    rw [ha', ← card_support_eq_three_iff, card_support_conj, ha0.card_support]
  have hb'3 : b'.IsThreeCycle := by
    rw [hb', ← card_support_eq_three_iff, card_support_conj, hb0.card_support]
  have hdis : Disjoint a' b' :=
    Equiv.Perm.Disjoint.conj (disjoint_iff_disjoint_support.mpr hab0) σ
  have hr1o : orderOf r1 = 3 := by rw [← orderOf_injective e hinj, he1]; exact ha'3.orderOf
  have hr2o : orderOf r2 = 3 := by rw [← orderOf_injective e hinj, he2]; exact hb'3.orderOf
  have hmemΓ : ∀ r : X, r ∈ (P : Subgroup X) → orderOf r = 3 → ∀ y : X,
      y * r * y⁻¹ ∈ Subgroup.zpowers r → y⁻¹ * r * y ∈ Subgroup.zpowers r →
      y ∈ gammaCore 3 1 ⊤ (P : Subgroup X) := by
    intro r hr hro y h1 h2
    refine Subgroup.subset_closure ⟨Subgroup.mem_top y, Subgroup.zpowers r,
      (Subgroup.zpowers_le).mpr hr, one_le_pRank_zpowers hro, ?_⟩
    exact mem_normalizer_zpowers h1 h2
  set Γ := gammaCore 3 1 ⊤ (P : Subgroup X) with hΓ
  have hN : ∀ r : X, r ∈ (P : Subgroup X) → orderOf r = 3 → ∀ k ∈ alternatingGroup (Fin n),
      k * e r = e r * k → k ∈ Γ.map e := by
    intro r hr hro k hk hkc
    obtain ⟨y, hy⟩ := hrange k hk
    have h1 : y * r * y⁻¹ = r := by
      apply hinj
      rw [map_mul, map_mul, map_inv, hy]
      calc k * e r * k⁻¹ = e r * k * k⁻¹ := by rw [hkc]
        _ = e r := by group
    have h2 : y⁻¹ * r * y = r := by
      apply hinj
      rw [map_mul, map_mul, map_inv, hy]
      calc k⁻¹ * e r * k = k⁻¹ * (k * e r) := by rw [hkc]; group
        _ = e r := by group
    refine ⟨y, hmemΓ r hr hro y ?_ ?_, hy⟩
    · rw [h1]; exact Subgroup.mem_zpowers r
    · rw [h2]; exact Subgroup.mem_zpowers r
  have hcard6 : (a'.support ∪ b'.support).card ≤ 6 := by
    calc (a'.support ∪ b'.support).card ≤ a'.support.card + b'.support.card :=
          Finset.card_union_le _ _
      _ = 6 := by rw [ha'3.card_support, hb'3.card_support]
  have hfree : ∃ r : Fin n, r ∉ a'.support ∧ r ∉ b'.support := by
    by_contra hcon
    push Not at hcon
    have hsub : (Finset.univ : Finset (Fin n)) ⊆ a'.support ∪ b'.support := by
      intro r _
      by_cases h1 : r ∈ a'.support
      · exact Finset.mem_union_left _ h1
      · exact Finset.mem_union_right _ (hcon r h1)
    have := Finset.card_le_card hsub
    simp only [Finset.card_univ, Fintype.card_fin] at this
    omega
  have hAlt : alternatingGroup (Fin n) ≤ Γ.map e :=
    CFSG.RankThree.PartOne.CTP.Alt.alternatingGroup_le_of_two_supports
      (disjoint_iff_disjoint_support.mp hdis) (by rw [ha'3.card_support])
      (by rw [hb'3.card_support]) hfree
      (fun k hk hkc => by
        have := hN r1 hg1 hr1o k hk (by rw [he1]; exact hkc)
        exact this)
      (fun k hk hkc => by
        have := hN r2 hg2 hr2o k hk (by rw [he2]; exact hkc)
        exact this)
  have hAltΓ : ∀ w : X, e w ∈ alternatingGroup (Fin n) → w ∈ Γ := by
    intro w hw
    obtain ⟨y, hy, hyw⟩ := hAlt hw
    rw [← hinj hyw]; exact hy
  rw [eq_top_iff]
  intro x _
  by_cases hx : e x ∈ alternatingGroup (Fin n)
  · exact hAltΓ x hx
  ·
    obtain ⟨c, hc⟩ : a'.support.Nonempty := by
      rw [← Finset.card_pos, ha'3.card_support]; norm_num
    have h1 := (ha'3.eq_swap_mul_swap_iff_mem_support (a := c)).mpr hc
    obtain ⟨hc1, hc2⟩ := List.nodup_cons.mp (ha'3.nodup_iff_mem_support.mpr hc)
    obtain ⟨hc3, -⟩ := List.nodup_cons.mp hc2
    simp only [List.mem_cons, not_or, List.not_mem_nil, or_false] at hc1 hc3
    set d := a' c with hd
    set f := a' d with hf
    have hcd : c ≠ d := hc1.1
    have hτ : Equiv.Perm.sign (swap c d) = -1 := Equiv.Perm.sign_swap hcd
    have hsx : Equiv.Perm.sign (e x) = -1 := by
      rcases Int.units_eq_one_or (Equiv.Perm.sign (e x)) with h | h
      · exact absurd (Equiv.Perm.mem_alternatingGroup.mpr h) hx
      · exact h
    have hμ : swap c d * (e x)⁻¹ ∈ alternatingGroup (Fin n) := by
      rw [Equiv.Perm.mem_alternatingGroup, map_mul, map_inv, hτ, hsx]; norm_num
    obtain ⟨z, hz⟩ := hrange _ hμ
    set y : X := z * x with hy
    have hey : e y = swap c d := by
      rw [hy, map_mul, hz]; group
    have hconj : swap c d * a' * (swap c d)⁻¹ = a'⁻¹ := by
      rw [h1]
      simp only [swap_inv, mul_inv_rev]
      rw [← mul_assoc, swap_mul_self, one_mul]
    have hyr1 : y * r1 * y⁻¹ = r1⁻¹ := by
      apply hinj
      rw [map_mul, map_mul, map_inv, map_inv, hey, he1]
      exact hconj
    have hyr1' : y⁻¹ * r1 * y = r1⁻¹ := by
      apply hinj
      rw [map_mul, map_mul, map_inv, map_inv, hey, he1]
      simpa [swap_inv] using hconj
    have hyΓ : y ∈ Γ := hmemΓ r1 hg1 hr1o y (by rw [hyr1]; exact Subgroup.inv_mem _ (Subgroup.mem_zpowers r1))
      (by rw [hyr1']; exact Subgroup.inv_mem _ (Subgroup.mem_zpowers r1))
    have hyx : y⁻¹ * x ∈ Γ := by
      apply hAltΓ
      rw [Equiv.Perm.mem_alternatingGroup, map_mul, map_inv, hey, map_mul, map_inv, hτ, hsx]
      norm_num
    have : x = y * (y⁻¹ * x) := by group
    rw [this]
    exact Γ.mul_mem hyΓ hyx

theorem gls3PlusCase_alternating_of_seven_le (n : ℕ) (h5 : 5 ≤ n) (h7 : 7 ≤ n) :
    Gls3PlusCase (.alternating n h5) := by
  unfold Gls3PlusCase
  intro X _ _ _ K hKn hKs hnc hiso hKc P hP hΓ
  exfalso
  obtain ⟨e⟩ := hiso
  have e' : ↥K ≃* ↥(alternatingGroup (Fin n)) := e
  have := hKn
  have h := gammaCore_eq_top_of_alt (K := K) h7 e' hKc P
  rw [h] at hΓ
  exact lt_irrefl _ hΓ

end Main


end CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank
