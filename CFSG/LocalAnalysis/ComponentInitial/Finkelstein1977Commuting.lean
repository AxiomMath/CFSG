module

public import CFSG.Assembly.ComponentTypeDefs

public section

namespace CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977

open CFSG.Assembly CFSG.Assembly.ComponentType

variable {G : Type*} [Group G]

theorem mem_conj_iff {H : Subgroup G} {g x : G} :
    x ∈ H.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * x * g ∈ H := by
  rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]

theorem conj_mem_conj {H : Subgroup G} {g x : G} (hx : x ∈ H) :
    g * x * g⁻¹ ∈ H.map (MulAut.conj g).toMonoidHom := by
  rw [mem_conj_iff]
  simpa [mul_assoc] using hx

theorem map_conj_mul (H : Subgroup G) (a b : G) :
    H.map (MulAut.conj (a * b)).toMonoidHom =
      (H.map (MulAut.conj b).toMonoidHom).map (MulAut.conj a).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [mul_assoc]

theorem map_conj_eq_of_mem_normalizer {H : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (H : Set G)) : H.map (MulAut.conj g).toMonoidHom = H := by
  ext x
  rw [mem_conj_iff]
  have h := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg)) x
  rw [inv_inv] at h
  exact h.symm

theorem card_map_conj (H : Subgroup G) (g : G) :
    Nat.card (H.map (MulAut.conj g).toMonoidHom) = Nat.card H :=
  Subgroup.card_map_of_injective (MulAut.conj g).injective

theorem mem_normalizer_of_even_orderOf_mem [Finite G] {L : Subgroup G}
    (hL : CFSG.Assembly.ComponentType.IsStandardSubgroup L) {a b x : G} (hx : Even (orderOf x))
    (hxa : x ∈ (Subgroup.centralizer (L : Set G)).map (MulAut.conj a).toMonoidHom)
    (hxb : x ∈ (Subgroup.centralizer (L : Set G)).map (MulAut.conj b).toMonoidHom) :
    a⁻¹ * b ∈ Subgroup.normalizer (Subgroup.centralizer (L : Set G) : Set G) := by
  obtain ⟨-, -, hodd, -, -⟩ := hL
  set C := Subgroup.centralizer (L : Set G)
  by_contra hnot
  have hy : a⁻¹ * x * a ∈ C ⊓ C.map (MulAut.conj (a⁻¹ * b)).toMonoidHom := by
    refine Subgroup.mem_inf.mpr ⟨mem_conj_iff.mp hxa, ?_⟩
    rw [mem_conj_iff]
    have := mem_conj_iff.mp hxb
    simpa [mul_assoc] using this
  have hord : orderOf (a⁻¹ * x * a) = orderOf x := by
    have h := MulEquiv.orderOf_eq (MulAut.conj a⁻¹) x
    rwa [MulAut.conj_apply, inv_inv] at h
  have hdvd := Subgroup.orderOf_dvd_natCard _ hy
  rw [hord] at hdvd
  exact (Nat.not_even_iff_odd.mpr (hodd _ hnot)) (even_iff_two_dvd.mpr (hx.two_dvd.trans hdvd))

theorem conj_eq_of_even_orderOf_mem [Finite G] {L : Subgroup G}
    (hL : CFSG.Assembly.ComponentType.IsStandardSubgroup L) {a b x : G} (hx : Even (orderOf x))
    (hxa : x ∈ (Subgroup.centralizer (L : Set G)).map (MulAut.conj a).toMonoidHom)
    (hxb : x ∈ (Subgroup.centralizer (L : Set G)).map (MulAut.conj b).toMonoidHom) :
    (Subgroup.centralizer (L : Set G)).map (MulAut.conj b).toMonoidHom =
      (Subgroup.centralizer (L : Set G)).map (MulAut.conj a).toMonoidHom := by
  have h := mem_normalizer_of_even_orderOf_mem hL hx hxa hxb
  rw [show b = a * (a⁻¹ * b) by group, map_conj_mul, map_conj_eq_of_mem_normalizer h]

theorem mem_normalizer_conj_of_commute [Finite G] {L : Subgroup G}
    (hL : CFSG.Assembly.ComponentType.IsStandardSubgroup L) {g x v : G} (hx : Even (orderOf x))
    (hxg : x ∈ (Subgroup.centralizer (L : Set G)).map (MulAut.conj g).toMonoidHom)
    (hvx : v * x = x * v) :
    v ∈ Subgroup.normalizer
      ((Subgroup.centralizer (L : Set G)).map (MulAut.conj g).toMonoidHom : Set G) := by
  set C := Subgroup.centralizer (L : Set G)
  have hxv : x ∈ C.map (MulAut.conj (v * g)).toMonoidHom := by
    rw [map_conj_mul]
    have h := conj_mem_conj (g := v) hxg
    rwa [hvx, mul_inv_cancel_right] at h
  have heq := conj_eq_of_even_orderOf_mem hL hx hxg hxv
  rw [map_conj_mul] at heq
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    rw [← heq]
    exact conj_mem_conj hy
  · intro hy
    rw [← heq, mem_conj_iff] at hy
    simpa [mul_assoc] using hy

theorem isCyclic_and_card_le_of_le [Finite G] {C : Subgroup G} (S : Sylow 2 C)
    (hS : IsCyclic S) {P : Subgroup G} (hPC : P ≤ C) (hP : IsPGroup 2 P) :
    IsCyclic P ∧ Nat.card P ≤ Nat.card S := by
  let e := Subgroup.subgroupOfEquivOfLe hPC
  have hP' : IsPGroup 2 (P.subgroupOf C) := hP.of_equiv e.symm
  obtain ⟨S₁, hS₁⟩ := hP'.exists_le_sylow
  let f : S₁ ≃* S := Sylow.equiv S₁ S
  have hS₁cyc : IsCyclic S₁ := isCyclic_of_injective f.toMonoidHom f.injective
  have hcyc : IsCyclic (P.subgroupOf C) :=
    isCyclic_of_injective (Subgroup.inclusion hS₁) (Subgroup.inclusion_injective hS₁)
  refine ⟨isCyclic_of_injective e.symm.toMonoidHom e.symm.injective, ?_⟩
  calc Nat.card P = Nat.card (P.subgroupOf C) := Nat.card_congr e.symm.toEquiv
    _ ≤ Nat.card S₁ := Subgroup.card_le_of_le hS₁
    _ = Nat.card S := Nat.card_congr f.toEquiv

theorem eq_of_orderOf_eq_two_of_isCyclic [Finite G] {P : Subgroup G} (hP : IsCyclic P)
    {a b : G} (ha : a ∈ P) (hb : b ∈ P) (ha2 : orderOf a = 2) (hb2 : orderOf b = 2) : a = b := by
  classical
  have h : Subgroup.zpowers (⟨a, ha⟩ : P) = Subgroup.zpowers ⟨b, hb⟩ :=
    IsCyclic.subgroup_eq_iff_card_eq.mpr (by
      rw [Nat.card_zpowers, Nat.card_zpowers, Subgroup.orderOf_mk, Subgroup.orderOf_mk, ha2, hb2])
  have hmem : (⟨a, ha⟩ : P) ∈ Subgroup.zpowers ⟨b, hb⟩ := h ▸ Subgroup.mem_zpowers _
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have hk' : b ^ k = a := by simpa using congrArg Subtype.val hk
  have hfin : IsOfFinOrder b := orderOf_pos_iff.mp (by rw [hb2]; norm_num)
  have ha' : a ∈ Subgroup.zpowers b := Subgroup.mem_zpowers_iff.mpr ⟨k, hk'⟩
  rw [hfin.mem_zpowers_iff_mem_range_orderOf, hb2] at ha'
  simp only [Finset.mem_image, Finset.mem_range] at ha'
  obtain ⟨j, hj, rfl⟩ := ha'
  interval_cases j
  · simp at ha2
  · simp

theorem eq_of_commute_of_orderOf_eq_two [Finite G] {C : Subgroup G}
    (hcyc : ∀ P : Subgroup G, P ≤ C → IsPGroup 2 P → IsCyclic P) {a b : G} (ha : a ∈ C)
    (hb : b ∈ C) (ha2 : orderOf a = 2) (hb2 : orderOf b = 2) (hab : a * b = b * a) : a = b := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hpa : IsPGroup 2 (Subgroup.zpowers a) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ha2, pow_one])
  have hpb : IsPGroup 2 (Subgroup.zpowers b) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hb2, pow_one])
  have hnorm : Subgroup.zpowers a ≤ Subgroup.normalizer (Subgroup.zpowers b : Set G) := by
    refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact ((Commute.zpow_left hab.symm j)).eq
  have hP := IsPGroup.to_sup_of_normal_right' hpa hpb hnorm
  have hle : Subgroup.zpowers a ⊔ Subgroup.zpowers b ≤ C :=
    sup_le (Subgroup.zpowers_le.mpr ha) (Subgroup.zpowers_le.mpr hb)
  exact eq_of_orderOf_eq_two_of_isCyclic (hcyc _ hle hP)
    (Subgroup.mem_sup_left (Subgroup.mem_zpowers a))
    (Subgroup.mem_sup_right (Subgroup.mem_zpowers b)) ha2 hb2

theorem commute_of_sq_commute {R : Subgroup G} (hRab : ∀ a ∈ R, ∀ b ∈ R, a * b = b * a)
    {s z : G} (hsR : s ∈ Subgroup.normalizer (R : Set G)) (hzs : z * s = s * z)
    (hz2 : z * z = 1) (hinv : ∀ w ∈ R, w * w = 1 → w = 1 ∨ w = z)
    (hsq : ∀ v ∈ R, v * s ^ 2 = s ^ 2 * v → v * s = s * v)
    {v : G} (hv : v ∈ R) (hv2 : v ^ 2 * s = s * v ^ 2) : v * s = s * v := by
  have hsv : s⁻¹ * v * s ∈ R := by
    have h := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hsR)) v
    rw [inv_inv] at h
    exact h.mp hv
  set w := v⁻¹ * (s⁻¹ * v * s) with hwdef
  have hwR : w ∈ R := Subgroup.mul_mem _ (Subgroup.inv_mem _ hv) hsv
  have hvw : v * w = w * v := hRab v hv w hwR
  have hv2' : v⁻¹ * v⁻¹ * s⁻¹ = s⁻¹ * v⁻¹ * v⁻¹ := by
    calc v⁻¹ * v⁻¹ * s⁻¹ = (s * v ^ 2)⁻¹ := by group
      _ = (v ^ 2 * s)⁻¹ := by rw [hv2]
      _ = s⁻¹ * v⁻¹ * v⁻¹ := by group
  have hconj : v⁻¹ * w * v = w⁻¹ := by
    calc v⁻¹ * w * v = v⁻¹ * v⁻¹ * s⁻¹ * v * s * v := by rw [hwdef]; group
      _ = s⁻¹ * v⁻¹ * v⁻¹ * v * s * v := by rw [hv2']
      _ = w⁻¹ := by rw [hwdef]; group
  have hww : w * w = 1 := by
    have h1 : v⁻¹ * w * v = w := by rw [mul_assoc, ← hvw, ← mul_assoc, inv_mul_cancel, one_mul]
    have h2 : w = w⁻¹ := h1.symm.trans hconj
    calc w * w = w * w⁻¹ := by rw [← h2]
      _ = 1 := mul_inv_cancel w
  rcases hinv w hwR hww with h1 | hz
  ·
    have h : s⁻¹ * v * s = v := by
      calc s⁻¹ * v * s = v * w := by rw [hwdef]; group
        _ = v := by rw [h1, mul_one]
    calc v * s = s * (s⁻¹ * v * s) := by group
      _ = s * v := by rw [h]
  ·
    have h : s⁻¹ * v * s = v * z := by
      calc s⁻¹ * v * s = v * w := by rw [hwdef]; group
        _ = v * z := by rw [hz]
    have hzs' : s⁻¹ * z * s = z := by rw [mul_assoc, hzs]; group
    have hs2 : s⁻¹ * (s⁻¹ * v * s) * s = v := by
      calc s⁻¹ * (s⁻¹ * v * s) * s = s⁻¹ * (v * z) * s := by rw [h]
        _ = (s⁻¹ * v * s) * (s⁻¹ * z * s) := by group
        _ = v * z * z := by rw [h, hzs', mul_assoc]
        _ = v := by rw [mul_assoc, hz2, mul_one]
    apply hsq v hv
    calc v * s ^ 2 = s ^ 2 * (s⁻¹ * (s⁻¹ * v * s) * s) := by simp only [sq]; group
      _ = s ^ 2 * v := by rw [hs2]

theorem commute_of_pow_two_pow_commute {R : Subgroup G} (hR : IsPGroup 2 R)
    (hRab : ∀ a ∈ R, ∀ b ∈ R, a * b = b * a)
    {s z : G} (hsR : s ∈ Subgroup.normalizer (R : Set G)) (hzs : z * s = s * z)
    (hz2 : z * z = 1) (hinv : ∀ w ∈ R, w * w = 1 → w = 1 ∨ w = z)
    (hsq : ∀ v ∈ R, v * s ^ 2 = s ^ 2 * v → v * s = s * v) :
    ∀ v ∈ R, v * s = s * v := by
  have key : ∀ k : ℕ, ∀ v ∈ R, v ^ (2 ^ k) * s = s * v ^ (2 ^ k) → v * s = s * v := by
    intro k
    induction k with
    | zero => intro v _ h; simpa using h
    | succ k ih =>
      intro v hv h
      have hv2R : v ^ 2 ∈ R := Subgroup.pow_mem _ hv 2
      have h' : (v ^ 2) ^ (2 ^ k) * s = s * (v ^ 2) ^ (2 ^ k) := by
        rwa [← pow_mul, ← pow_succ']
      exact commute_of_sq_commute hRab hsR hzs hz2 hinv hsq hv (ih (v ^ 2) hv2R h')
  intro v hv
  obtain ⟨k, hk⟩ := hR ⟨v, hv⟩
  have hk' : v ^ (2 ^ k) = 1 := by simpa using congrArg Subtype.val hk
  exact key k v hv (by rw [hk', one_mul, mul_one])

theorem exists_twoSubgroup_inf_card_ge [Finite G] {N C : Subgroup G} (hCN : C ≤ N)
    (hNC : N ≤ Subgroup.normalizer (C : Set G)) {S₀ : Subgroup G} (hS₀C : S₀ ≤ C)
    (hS₀ : IsPGroup 2 S₀) {X : Subgroup G} (hXN : X ≤ N) (hX : IsPGroup 2 X) :
    ∃ Y : Subgroup G, X ≤ Y ∧ Y ≤ N ∧ IsPGroup 2 Y ∧
      Nat.card S₀ ≤ Nat.card (Y ⊓ C : Subgroup G) := by
  have hX' : IsPGroup 2 (X.subgroupOf N) := hX.of_equiv (Subgroup.subgroupOfEquivOfLe hXN).symm
  have hS₀' : IsPGroup 2 (S₀.subgroupOf N) :=
    hS₀.of_equiv (Subgroup.subgroupOfEquivOfLe (hS₀C.trans hCN)).symm
  obtain ⟨Q₂, hQ₂⟩ := hX'.exists_le_sylow
  obtain ⟨Q₁, hQ₁⟩ := hS₀'.exists_le_sylow
  obtain ⟨n, hn⟩ := MulAction.exists_smul_eq N Q₁ Q₂
  refine ⟨(Q₂ : Subgroup N).map N.subtype, ?_, Subgroup.map_subtype_le _,
    Q₂.isPGroup'.map _, ?_⟩
  · intro x hx
    exact ⟨⟨x, hXN hx⟩, hQ₂ (Subgroup.mem_subgroupOf.mpr hx), rfl⟩
  · have hle : S₀.map (MulAut.conj (n : G)).toMonoidHom ≤
        (Q₂ : Subgroup N).map N.subtype ⊓ C := by
      rintro _ ⟨y, hy, rfl⟩
      refine ⟨?_, ?_⟩
      · have hyQ : (⟨y, hCN (hS₀C hy)⟩ : N) ∈ (Q₁ : Subgroup N) :=
          hQ₁ (Subgroup.mem_subgroupOf.mpr hy)
        have hmem : n * ⟨y, hCN (hS₀C hy)⟩ * n⁻¹ ∈ (Q₂ : Subgroup N) := by
          rw [← hn, Sylow.coe_subgroup_smul]
          exact Subgroup.mem_pointwise_smul_iff_inv_smul_mem.mpr (by simpa [mul_assoc] using hyQ)
        exact ⟨_, hmem, rfl⟩
      · exact (Subgroup.mem_normalizer_iff.mp (hNC n.2) y).mp (hS₀C hy)
    calc Nat.card S₀ = Nat.card (S₀.map (MulAut.conj (n : G)).toMonoidHom) :=
          (card_map_conj S₀ n).symm
      _ ≤ _ := Subgroup.card_le_of_le hle

end CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977
