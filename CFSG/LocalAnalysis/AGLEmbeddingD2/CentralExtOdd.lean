module

public import CFSG.GroupTheory.AbelianNormalCoprimeComplementLifting
public import CFSG.LocalAnalysis.SectionRank.Sporadic.LocalWitness

public section

namespace CFSG.AGLEmbeddingD2.CentralExt

open scoped commutatorElement Pointwise

section Commutators

variable {G : Type*} [Group G]

theorem commutatorElement_mul_left_of_mem_center {a b k : G} (hk : k ∈ Subgroup.center G) :
    ⁅a * k, b⁆ = ⁅a, b⁆ := by
  have hkb : b * k = k * b := Subgroup.mem_center_iff.mp hk b
  rw [commutatorElement_def, commutatorElement_def]
  calc a * k * b * (a * k)⁻¹ * b⁻¹ = a * (k * b) * k⁻¹ * a⁻¹ * b⁻¹ := by group
    _ = a * (b * k) * k⁻¹ * a⁻¹ * b⁻¹ := by rw [hkb]
    _ = a * b * a⁻¹ * b⁻¹ := by group

theorem commutatorElement_mul_right_of_mem_center {a b k : G} (hk : k ∈ Subgroup.center G) :
    ⁅a, b * k⁆ = ⁅a, b⁆ := by
  calc ⁅a, b * k⁆ = ⁅b * k, a⁆⁻¹ := (commutatorElement_inv _ _).symm
    _ = ⁅b, a⁆⁻¹ := by rw [commutatorElement_mul_left_of_mem_center hk]
    _ = ⁅a, b⁆ := commutatorElement_inv _ _

theorem commutatorElement_pow_right {a b : G} (h : Commute ⁅a, b⁆ b) (n : ℕ) :
    ⁅a, b⁆ ^ n = ⁅a, b ^ n⁆ := by
  have h' : Commute ⁅b, a⁆ b := by rw [← commutatorElement_inv]; exact h.inv_left
  calc ⁅a, b⁆ ^ n = (⁅b, a⁆ ^ n)⁻¹ := by rw [← commutatorElement_inv a b, inv_pow, inv_inv]
    _ = ⁅b ^ n, a⁆⁻¹ := by rw [CFSG.SectionRank.LocalWitness.commutator_pow_eq h' n]
    _ = ⁅a, b ^ n⁆ := commutatorElement_inv _ _

theorem commutatorElement_pow_pow {a b : G} (ha : Commute ⁅a, b⁆ a) (hb : Commute ⁅a, b⁆ b)
    (m n : ℕ) : ⁅a ^ m, b ^ n⁆ = ⁅a, b⁆ ^ (m * n) := by
  have h1 : ⁅a ^ m, b⁆ = ⁅a, b⁆ ^ m := (CFSG.SectionRank.LocalWitness.commutator_pow_eq ha m).symm
  have h2 : Commute ⁅a ^ m, b⁆ b := by rw [h1]; exact hb.pow_left m
  rw [← commutatorElement_pow_right h2 n, h1, pow_mul]

theorem conj_commutatorElement (h a b : G) :
    h * ⁅a, b⁆ * h⁻¹ = ⁅h * a * h⁻¹, h * b * h⁻¹⁆ := by
  simp only [commutatorElement_def]
  group

theorem commute_of_mem_center {k : G} (hk : k ∈ Subgroup.center G) (g : G) : Commute k g :=
  (Subgroup.mem_center_iff.mp hk g).symm

theorem commute_of_mem_closure_pair {x y : G} (hxy : x * y = y * x) {a b : G}
    (ha : a ∈ Subgroup.closure ({x, y} : Set G)) (hb : b ∈ Subgroup.closure ({x, y} : Set G)) :
    a * b = b * a := by
  have h1 : Subgroup.closure ({x, y} : Set G) ≤ Subgroup.centralizer ({x, y} : Set G) := by
    rw [Subgroup.closure_le]
    rintro s (rfl | rfl) <;> rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff] <;>
      rintro t (rfl | rfl)
    · rfl
    · exact hxy.symm
    · exact hxy
    · rfl
  have h2 : Subgroup.closure ({x, y} : Set G) ≤ Subgroup.centralizer ({a} : Set G) := by
    rw [Subgroup.closure_le]
    rintro s hs
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    rintro t rfl
    exact (Subgroup.mem_centralizer_iff.mp (h1 ha) s hs).symm
  exact Subgroup.mem_centralizer_iff.mp (h2 hb) a rfl

end Commutators

section CentralExt

variable {Γ T : Type*} [Group Γ] [Finite Γ] [Group T] {φ : Γ →* T}

theorem exists_map_eq_conj {p : ℕ} [Fact p.Prime] [Finite T] (hφ : Function.Surjective φ)
    (P : Sylow p Γ) (Q : Subgroup T) (hQ : Nat.card Q = p ^ (Nat.card T).factorization p) :
    ∃ g : T, (P : Subgroup Γ).map φ = Q.map (MulAut.conj g).toMonoidHom := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq T (Sylow.ofCard Q hQ) (P.mapSurjective hφ)
  refine ⟨g, ?_⟩
  have := congrArg (fun S : Sylow p T => (S : Subgroup T)) hg
  simp only [Sylow.coe_subgroup_smul, Sylow.coe_ofCard, Sylow.coe_mapSurjective] at this
  rw [← this, Subgroup.pointwise_smul_def]
  rfl

theorem map_conj_closure_pair (g x y : T) :
    (Subgroup.closure ({x, y} : Set T)).map (MulAut.conj g).toMonoidHom =
      Subgroup.closure ({MulAut.conj g x, MulAut.conj g y} : Set T) := by
  rw [MonoidHom.map_closure, Set.image_pair]
  rfl

theorem eq_one_of_complement {p : ℕ} [hp : Fact p.Prime] (hφ : Function.Surjective φ)
    (hker : φ.ker ≤ Subgroup.center Γ) {C : Subgroup Γ} (hC : C ⊓ φ.ker = ⊥)
    (hCcard : Nat.card C = p ^ (Nat.card T).factorization p) {z : Γ}
    (hz : z ∈ φ.ker ⊓ commutator Γ) (hzp : IsPGroup p (Subgroup.zpowers z)) : z = 1 := by
  have : Finite T := Finite.of_surjective φ hφ
  obtain ⟨P, hCP⟩ := (IsPGroup.of_card hCcard).exists_le_sylow
  have hinj : Function.Injective (φ.comp C.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro c hc
    have hc' : (c : Γ) ∈ C ⊓ φ.ker := ⟨c.2, hc⟩
    rw [hC, Subgroup.mem_bot] at hc'
    exact Subtype.ext hc'
  have hrange : (φ.comp C.subtype).range = C.map φ := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hCmap : Nat.card (C.map φ) = Nat.card C := by
    rw [← hrange]
    exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  have hPmap : (P : Subgroup Γ).map φ = C.map φ := by
    refine (Subgroup.eq_of_le_of_card_ge (Subgroup.map_mono hCP) ?_).symm
    rw [hCmap, hCcard]
    have h := (P.mapSurjective hφ).card_eq_multiplicity
    rw [Sylow.coe_mapSurjective] at h
    rw [h]
  set N : Subgroup Γ := φ.ker ⊓ P with hN
  have hNc : N ≤ Subgroup.center Γ := inf_le_left.trans hker
  have : N.Normal := Subgroup.normal_of_le_center hNc
  have : IsMulCommutative N :=
    ⟨⟨fun a b => Subtype.ext (Subgroup.mem_center_iff.mp (hNc b.2) a)⟩⟩
  have hsup : N ⊔ C = P := by
    refine le_antisymm (sup_le inf_le_right hCP) fun g hg => ?_
    have hgm : φ g ∈ C.map φ := hPmap ▸ Subgroup.mem_map_of_mem φ hg
    obtain ⟨c, hc, hcg⟩ := Subgroup.mem_map.mp hgm
    have hk : c⁻¹ * g ∈ N :=
      ⟨MonoidHom.mem_ker.mpr (by rw [map_mul, map_inv, hcg, inv_mul_cancel]),
        P.mul_mem (P.inv_mem (hCP hc)) hg⟩
    have h := Subgroup.mul_mem_sup hc hk
    rw [mul_inv_cancel_left] at h
    rwa [sup_comm]
  have hNK : N ⊓ C = ⊥ := by
    rw [eq_bot_iff, ← hC]
    exact fun g hg => ⟨hg.2, hg.1.1⟩
  have hNp : IsPGroup p N := P.isPGroup'.to_le inf_le_right
  obtain ⟨k, hk⟩ := hNp.exists_card_eq
  have hcop : Nat.Coprime (P : Subgroup Γ).index (Nat.card N) := by
    rw [hk]
    exact Nat.Coprime.pow_right _
      ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr P.not_dvd_index).symm
  obtain ⟨D, -, hND, hNDtop⟩ :=
    CFSG.GroupTheory.abelian_normal_coprime_index_complement_lifting N P C hcop hNK hsup
  have hmem : ∀ g : Γ, ∃ n ∈ N, ∃ d ∈ D, n * d = g := fun g =>
    Subgroup.mem_sup_of_normal_left.mp (by rw [hNDtop]; exact Subgroup.mem_top g)
  have hDcomm : commutator Γ ≤ D := by
    rw [commutator_def, Subgroup.commutator_le]
    intro g _ g' _
    obtain ⟨n, hn, d, hd, rfl⟩ := hmem g
    obtain ⟨n', hn', d', hd', rfl⟩ := hmem g'
    rw [(commute_of_mem_center (hNc hn) d).eq, (commute_of_mem_center (hNc hn') d').eq,
      commutatorElement_mul_left_of_mem_center (hNc hn),
      commutatorElement_mul_right_of_mem_center (hNc hn'), commutatorElement_def]
    exact D.mul_mem (D.mul_mem (D.mul_mem hd hd') (D.inv_mem hd)) (D.inv_mem hd')
  have hzc : Subgroup.zpowers z ≤ Subgroup.center Γ := Subgroup.zpowers_le.mpr (hker hz.1)
  have : (Subgroup.zpowers z).Normal := Subgroup.normal_of_le_center hzc
  have hzP : z ∈ P := hzp.le_sylow_of_normal P (Subgroup.mem_zpowers z)
  have hzND : z ∈ N ⊓ D := ⟨⟨hz.1, hzP⟩, hDcomm hz.2⟩
  rwa [hND, Subgroup.mem_bot] at hzND

theorem isMulCommutative_sylow_of_not_sq_dvd {p : ℕ} [hp : Fact p.Prime]
    (hφ : Function.Surjective φ) (hker : φ.ker ≤ Subgroup.center Γ)
    (hT : ¬ p ^ 2 ∣ Nat.card T) (P : Sylow p Γ) : IsMulCommutative (P : Subgroup Γ) := by
  have : Finite T := Finite.of_surjective φ hφ
  have hcomm : ∀ a ∈ (P : Subgroup Γ), ∀ b ∈ (P : Subgroup Γ), a * b = b * a := by
    intro a ha b hb
    by_cases ha1 : φ a = 1
    · exact (Subgroup.mem_center_iff.mp (hker ha1) b).symm
    set Q : Subgroup T := (P : Subgroup Γ).map φ with hQ
    obtain ⟨k, hk⟩ := (P.isPGroup'.map φ).exists_card_eq
    have hk1 : k ≤ 1 := by
      by_contra h
      exact hT ((pow_dvd_pow p (by omega : 2 ≤ k)).trans (hk ▸ Subgroup.card_subgroup_dvd_card Q))
    have hmem : φ a ∈ Q := Subgroup.mem_map_of_mem φ ha
    have hord : orderOf (φ a) ∣ p ^ k := hk ▸ Subgroup.orderOf_dvd_natCard Q hmem
    have hord1 : orderOf (φ a) ≠ 1 := fun h => ha1 (orderOf_eq_one_iff.mp h)
    have hk' : k = 1 := by
      interval_cases k
      · exact absurd (Nat.dvd_one.mp (by simpa using hord)) hord1
      · rfl
    subst hk'
    have hordp : orderOf (φ a) = p :=
      ((Nat.dvd_prime hp.out).mp (by simpa using hord)).resolve_left hord1
    have hQeq : Subgroup.zpowers (φ a) = Q :=
      Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hmem)
        (by rw [Nat.card_zpowers, hordp, hk, pow_one])
    have hbm : φ b ∈ Subgroup.zpowers (φ a) := hQeq ▸ Subgroup.mem_map_of_mem φ hb
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hbm
    obtain ⟨c, hc, rfl⟩ : ∃ c ∈ Subgroup.center Γ, b = a ^ m * c :=
      ⟨(a ^ m)⁻¹ * b, hker (by rw [MonoidHom.mem_ker, map_mul, map_inv, map_zpow, hm,
        inv_mul_cancel]), by group⟩
    calc a * (a ^ m * c) = a ^ m * a * c := by
          rw [← mul_assoc, ((Commute.refl a).zpow_right m).eq]
      _ = a ^ m * (c * a) := by rw [mul_assoc, (commute_of_mem_center hc a).eq]
      _ = a ^ m * c * a := by rw [mul_assoc]
  exact ⟨⟨fun a b => Subtype.ext (hcomm a a.2 b b.2)⟩⟩

omit [Finite Γ] in
theorem commute_lift_of_square (hker : φ.ker ≤ Subgroup.center Γ) {x y h : T}
    (hxy : x * y = y * x) (hhx : h * x * h⁻¹ = x) (hhy : h * y * h⁻¹ = x ^ 2 * y ^ 2)
    {x' y' h' : Γ} (hx : φ x' = x) (hy : φ y' = y) (hh : φ h' = h) : x' * y' = y' * x' := by
  have hc : ⁅x', y'⁆ ∈ Subgroup.center Γ := hker (by
    rw [MonoidHom.mem_ker, map_commutatorElement, hx, hy,
      commutatorElement_eq_one_iff_mul_comm.mpr hxy])
  obtain ⟨k₁, hk₁, e₁⟩ : ∃ k ∈ φ.ker, h' * x' * h'⁻¹ = x' * k :=
    ⟨x'⁻¹ * (h' * x' * h'⁻¹), by
      simp only [MonoidHom.mem_ker, map_mul, map_inv, hx, hh, hhx, inv_mul_cancel],
      by rw [mul_inv_cancel_left]⟩
  obtain ⟨k₂, hk₂, e₂⟩ : ∃ k ∈ φ.ker, h' * y' * h'⁻¹ = x' ^ 2 * y' ^ 2 * k :=
    ⟨(x' ^ 2 * y' ^ 2)⁻¹ * (h' * y' * h'⁻¹), by
      simp only [MonoidHom.mem_ker, map_mul, map_inv, map_pow, hx, hy, hh, hhy, inv_mul_cancel],
      by rw [mul_inv_cancel_left]⟩
  have h1 : h' * ⁅x', y'⁆ * h'⁻¹ = ⁅x', y'⁆ := by
    rw [(commute_of_mem_center hc h').symm.eq, mul_inv_cancel_right]
  have hc2 : ⁅x', y' ^ 2⁆ = ⁅x', y'⁆ ^ 2 :=
    (commutatorElement_pow_right (commute_of_mem_center hc y') 2).symm
  have hc2c : ⁅x', y'⁆ ^ 2 ∈ Subgroup.center Γ := (Subgroup.center Γ).pow_mem hc 2
  have h2 : h' * ⁅x', y'⁆ * h'⁻¹ = ⁅x', y'⁆ ^ 2 := by
    rw [conj_commutatorElement, e₁, e₂, commutatorElement_mul_left_of_mem_center (hker hk₁),
      commutatorElement_mul_right_of_mem_center (hker hk₂)]
    calc ⁅x', x' ^ 2 * y' ^ 2⁆ = x' ^ 2 * ⁅x', y' ^ 2⁆ * (x' ^ 2)⁻¹ := by
          simp only [commutatorElement_def]
          group
      _ = ⁅x', y'⁆ ^ 2 := by
          rw [hc2, (commute_of_mem_center hc2c (x' ^ 2)).symm.eq, mul_inv_cancel_right]
  have hcc : ⁅x', y'⁆ * ⁅x', y'⁆ = ⁅x', y'⁆ := by rw [← pow_two, ← h2, h1]
  exact commutatorElement_eq_one_iff_mul_comm.mp (mul_eq_left.mp hcc)

theorem isMulCommutative_sylow_of_square {p : ℕ} [Fact p.Prime] (hφ : Function.Surjective φ)
    (hker : φ.ker ≤ Subgroup.center Γ) {x y h : T} (hxy : x * y = y * x)
    (hcard : Nat.card (Subgroup.closure ({x, y} : Set T)) = p ^ (Nat.card T).factorization p)
    (hhx : h * x * h⁻¹ = x) (hhy : h * y * h⁻¹ = x ^ 2 * y ^ 2) (P : Sylow p Γ) :
    IsMulCommutative (P : Subgroup Γ) := by
  have : Finite T := Finite.of_surjective φ hφ
  obtain ⟨g, hg⟩ := exists_map_eq_conj hφ P _ hcard
  obtain ⟨x', hx⟩ := hφ (MulAut.conj g x)
  obtain ⟨y', hy⟩ := hφ (MulAut.conj g y)
  obtain ⟨h', hh⟩ := hφ (MulAut.conj g h)
  have hxy' : MulAut.conj g x * MulAut.conj g y = MulAut.conj g y * MulAut.conj g x := by
    rw [← map_mul, hxy, map_mul]
  have hhx' : MulAut.conj g h * MulAut.conj g x * (MulAut.conj g h)⁻¹ = MulAut.conj g x := by
    rw [← map_inv, ← map_mul, ← map_mul, hhx]
  have hhy' : MulAut.conj g h * MulAut.conj g y * (MulAut.conj g h)⁻¹ =
      MulAut.conj g x ^ 2 * MulAut.conj g y ^ 2 := by
    rw [← map_inv, ← map_mul, ← map_mul, hhy, map_mul, map_pow, map_pow]
  have hc := commute_lift_of_square hker hxy' hhx' hhy' hx hy hh
  have hPle : (P : Subgroup Γ).map φ ≤ (Subgroup.closure ({x', y'} : Set Γ)).map φ := by
    rw [hg, map_conj_closure_pair, MonoidHom.map_closure, Set.image_pair, hx, hy]
  have hdecomp : ∀ a ∈ (P : Subgroup Γ), ∃ a' ∈ Subgroup.closure ({x', y'} : Set Γ),
      ∃ k ∈ Subgroup.center Γ, a = a' * k := by
    intro a ha
    obtain ⟨a', ha', he⟩ := Subgroup.mem_map.mp (hPle (Subgroup.mem_map_of_mem φ ha))
    exact ⟨a', ha', a'⁻¹ * a, hker (by rw [MonoidHom.mem_ker, map_mul, map_inv, he,
      inv_mul_cancel]), by group⟩
  refine ⟨⟨fun a b => Subtype.ext ?_⟩⟩
  obtain ⟨a', ha', k, hk, hak⟩ := hdecomp a a.2
  obtain ⟨b', hb', l, hl, hbl⟩ := hdecomp b b.2
  change (a : Γ) * b = b * a
  rw [hak, hbl]
  have hab := commute_of_mem_closure_pair hc ha' hb'
  calc a' * k * (b' * l) = a' * (k * b') * l := by group
    _ = a' * (b' * k) * l := by rw [(commute_of_mem_center hk b').eq]
    _ = a' * b' * (k * l) := by group
    _ = b' * a' * (l * k) := by rw [hab, (commute_of_mem_center hk l).eq]
    _ = b' * (a' * l) * k := by group
    _ = b' * (l * a') * k := by rw [(commute_of_mem_center hl a').symm.eq]
    _ = b' * l * (a' * k) := by group

omit [Finite Γ] in
theorem exists_lift_of_cubic (hker : φ.ker ≤ Subgroup.center Γ) {x y h : T}
    (hx5 : x ^ 5 = 1) (hy5 : y ^ 5 = 1) (hzx : Commute ⁅x, y⁆ x) (hzy : Commute ⁅x, y⁆ y)
    (hhx : h * x * h⁻¹ = x ^ 3) (hhy : h * y * h⁻¹ = y ^ 3)
    (hhz : h * ⁅x, y⁆ * h⁻¹ = ⁅x, y⁆ ^ 4) {x' y' h' : Γ} (hx : φ x' = x) (hy : φ y' = y)
    (hh : φ h' = h) (hxo : ∃ f : ℕ, orderOf (x' ^ 5) = 5 ^ f)
    (hyo : ∃ f : ℕ, orderOf (y' ^ 5) = 5 ^ f) :
    ∃ x'' y'' : Γ, φ x'' = x ∧ φ y'' = y ∧ x'' ^ 5 = 1 ∧ y'' ^ 5 = 1 ∧
      Commute ⁅x'', y''⁆ x'' ∧ Commute ⁅x'', y''⁆ y'' := by
  have hcz : φ ⁅x', y'⁆ = ⁅x, y⁆ := by rw [map_commutatorElement, hx, hy]
  obtain ⟨k₃, hk₃, e₃⟩ : ∃ k ∈ φ.ker, h' * ⁅x', y'⁆ * h'⁻¹ = ⁅x', y'⁆ ^ 4 * k :=
    ⟨(⁅x', y'⁆ ^ 4)⁻¹ * (h' * ⁅x', y'⁆ * h'⁻¹), by
      simp only [MonoidHom.mem_ker, map_mul, map_inv, map_pow, hcz, hh, hhz, inv_mul_cancel],
      by rw [mul_inv_cancel_left]⟩
  obtain ⟨k₁, hk₁, e₁⟩ : ∃ k ∈ φ.ker, h' * x' * h'⁻¹ = x' ^ 3 * k :=
    ⟨(x' ^ 3)⁻¹ * (h' * x' * h'⁻¹), by
      simp only [MonoidHom.mem_ker, map_mul, map_inv, map_pow, hx, hh, hhx, inv_mul_cancel],
      by rw [mul_inv_cancel_left]⟩
  obtain ⟨k₂, hk₂, e₂⟩ : ∃ k ∈ φ.ker, h' * y' * h'⁻¹ = y' ^ 3 * k :=
    ⟨(y' ^ 3)⁻¹ * (h' * y' * h'⁻¹), by
      simp only [MonoidHom.mem_ker, map_mul, map_inv, map_pow, hy, hh, hhy, inv_mul_cancel],
      by rw [mul_inv_cancel_left]⟩
  have hkill : ∀ {w k : Γ}, k ∈ φ.ker → h' * w * h'⁻¹ = w ^ 3 * k →
      φ ⁅⁅x', y'⁆, w⁆ = 1 → φ (w ^ 5) = 1 → ⁅⁅x', y'⁆, w⁆ = 1 := by
    intro w k hk e hφa hφw
    have ha : ⁅⁅x', y'⁆, w⁆ ∈ Subgroup.center Γ := hker hφa
    have hw5 : w ^ 5 ∈ Subgroup.center Γ := hker hφw
    have h5 : ⁅⁅x', y'⁆, w⁆ ^ 5 = 1 := by
      rw [commutatorElement_pow_right (commute_of_mem_center ha w),
        commutatorElement_eq_one_iff_mul_comm]
      exact (commute_of_mem_center hw5 _).symm.eq
    have h12 : ⁅⁅x', y'⁆, w⁆ = ⁅⁅x', y'⁆, w⁆ ^ 11 * ⁅⁅x', y'⁆, w⁆ := by
      calc ⁅⁅x', y'⁆, w⁆ = h' * ⁅⁅x', y'⁆, w⁆ * h'⁻¹ := by
            rw [(commute_of_mem_center ha h').symm.eq, mul_inv_cancel_right]
        _ = ⁅h' * ⁅x', y'⁆ * h'⁻¹, h' * w * h'⁻¹⁆ := conj_commutatorElement _ _ _
        _ = ⁅⁅x', y'⁆ ^ 4 * k₃, w ^ 3 * k⁆ := by rw [e₃, e]
        _ = ⁅⁅x', y'⁆ ^ 4, w ^ 3⁆ := by
            rw [commutatorElement_mul_left_of_mem_center (hker hk₃),
              commutatorElement_mul_right_of_mem_center (hker hk)]
        _ = ⁅⁅x', y'⁆, w⁆ ^ (4 * 3) :=
            commutatorElement_pow_pow (commute_of_mem_center ha _) (commute_of_mem_center ha w) 4 3
        _ = ⁅⁅x', y'⁆, w⁆ ^ 11 * ⁅⁅x', y'⁆, w⁆ := by rw [← pow_succ]
    have h11 : ⁅⁅x', y'⁆, w⁆ ^ 11 = 1 := mul_eq_right.mp h12.symm
    have hdvd : orderOf ⁅⁅x', y'⁆, w⁆ ∣ Nat.gcd 5 11 :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h5) (orderOf_dvd_of_pow_eq_one h11)
    rwa [show Nat.gcd 5 11 = 1 by norm_num, Nat.dvd_one, orderOf_eq_one_iff] at hdvd
  have hcx : Commute ⁅x', y'⁆ x' := commutatorElement_eq_one_iff_mul_comm.mp
    (hkill hk₁ e₁ (by rw [map_commutatorElement, hcz, hx,
      commutatorElement_eq_one_iff_mul_comm.mpr hzx]) (by rw [map_pow, hx, hx5]))
  have hcy : Commute ⁅x', y'⁆ y' := commutatorElement_eq_one_iff_mul_comm.mp
    (hkill hk₂ e₂ (by rw [map_commutatorElement, hcz, hy,
      commutatorElement_eq_one_iff_mul_comm.mpr hzy]) (by rw [map_pow, hy, hy5]))
  have hfix : ∀ {w k : Γ}, k ∈ φ.ker → h' * w * h'⁻¹ = w ^ 3 * k → φ (w ^ 5) = 1 →
      (∃ f : ℕ, orderOf (w ^ 5) = 5 ^ f) → ∃ v ∈ φ.ker, (w * v) ^ 5 = 1 := by
    intro w k hk e hφw ⟨f, hf⟩
    have hkc := hker hk
    have hw5 : w ^ 5 ∈ Subgroup.center Γ := hker hφw
    have e5 : w ^ 5 = w ^ 5 * ((w ^ 5) ^ 2 * k ^ 5) := by
      calc w ^ 5 = h' * w ^ 5 * h'⁻¹ := by
            rw [(commute_of_mem_center hw5 h').symm.eq, mul_inv_cancel_right]
        _ = (h' * w * h'⁻¹) ^ 5 := conj_pow.symm
        _ = (w ^ 3 * k) ^ 5 := by rw [e]
        _ = (w ^ 3) ^ 5 * k ^ 5 := (commute_of_mem_center hkc _).symm.mul_pow 5
        _ = w ^ 5 * ((w ^ 5) ^ 2 * k ^ 5) := by group
    have hone : (w ^ 5) ^ 2 * k ^ 5 = 1 := left_eq_mul.mp e5
    have hodd : 2 * ((5 ^ f + 1) / 2) = 5 ^ f + 1 :=
      Nat.two_mul_div_two_of_even (Odd.pow (by decide : Odd 5)).add_one
    refine ⟨k ^ ((5 ^ f + 1) / 2), (φ.ker).pow_mem hk _, ?_⟩
    have hvc : k ^ ((5 ^ f + 1) / 2) ∈ Subgroup.center Γ := (Subgroup.center Γ).pow_mem hkc _
    have hα : w ^ 5 = ((w ^ 5) ^ 2) ^ ((5 ^ f + 1) / 2) := by
      calc w ^ 5 = (w ^ 5) ^ (5 ^ f + 1) := by
            rw [pow_succ (w ^ 5) (5 ^ f), ← hf, pow_orderOf_eq_one, one_mul]
        _ = ((w ^ 5) ^ 2) ^ ((5 ^ f + 1) / 2) := by rw [← pow_mul (w ^ 5) 2, hodd]
    rw [(commute_of_mem_center hvc w).symm.mul_pow, ← pow_mul k, mul_comm ((5 ^ f + 1) / 2) 5,
      pow_mul k 5, hα, eq_inv_of_mul_eq_one_left hone, inv_pow, inv_mul_cancel]
  obtain ⟨v₁, hv₁, hxv⟩ := hfix hk₁ e₁ (by rw [map_pow, hx, hx5]) hxo
  obtain ⟨v₂, hv₂, hyv⟩ := hfix hk₂ e₂ (by rw [map_pow, hy, hy5]) hyo
  have hcomm : ⁅x' * v₁, y' * v₂⁆ = ⁅x', y'⁆ := by
    rw [commutatorElement_mul_left_of_mem_center (hker hv₁),
      commutatorElement_mul_right_of_mem_center (hker hv₂)]
  refine ⟨x' * v₁, y' * v₂, by rw [map_mul, MonoidHom.mem_ker.mp hv₁, mul_one, hx],
    by rw [map_mul, MonoidHom.mem_ker.mp hv₂, mul_one, hy], hxv, hyv, ?_, ?_⟩
  · rw [hcomm]
    exact hcx.mul_right (commute_of_mem_center (hker hv₁) _).symm
  · rw [hcomm]
    exact hcy.mul_right (commute_of_mem_center (hker hv₂) _).symm

theorem exists_complement_of_cubic (hφ : Function.Surjective φ)
    (hker : φ.ker ≤ Subgroup.center Γ) {x y h : T} (hx5 : x ^ 5 = 1) (hy5 : y ^ 5 = 1)
    (hzx : Commute ⁅x, y⁆ x) (hzy : Commute ⁅x, y⁆ y)
    (hcard : Nat.card (Subgroup.closure ({x, y} : Set T)) = 5 ^ 3)
    (hT : (Nat.card T).factorization 5 = 3)
    (hhx : h * x * h⁻¹ = x ^ 3) (hhy : h * y * h⁻¹ = y ^ 3)
    (hhz : h * ⁅x, y⁆ * h⁻¹ = ⁅x, y⁆ ^ 4) :
    ∃ C : Subgroup Γ, C ⊓ φ.ker = ⊥ ∧ Nat.card C = 5 ^ (Nat.card T).factorization 5 := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have : Finite T := Finite.of_surjective φ hφ
  obtain ⟨P⟩ : Nonempty (Sylow 5 Γ) := inferInstance
  obtain ⟨g, hg⟩ := exists_map_eq_conj hφ P _ (hcard.trans (by rw [hT]))
  have hmemP : ∀ t ∈ ({x, y} : Set T), MulAut.conj g t ∈ (P : Subgroup Γ).map φ := by
    intro t ht
    rw [hg]
    exact Subgroup.mem_map_of_mem _ (Subgroup.subset_closure ht)
  obtain ⟨x', hx'P, hx⟩ := Subgroup.mem_map.mp (hmemP x (by simp))
  obtain ⟨y', hy'P, hy⟩ := Subgroup.mem_map.mp (hmemP y (by simp))
  obtain ⟨h', hh⟩ := hφ (MulAut.conj g h)
  have hord : ∀ w ∈ (P : Subgroup Γ), ∃ f : ℕ, orderOf (w ^ 5) = 5 ^ f := by
    intro w hw
    obtain ⟨n, hn⟩ := P.isPGroup' ⟨w ^ 5, P.pow_mem hw 5⟩
    have h1 : (w ^ 5) ^ 5 ^ n = 1 := by simpa using congrArg Subtype.val hn
    obtain ⟨f, -, hf⟩ := (Nat.dvd_prime_pow Nat.prime_five).mp (orderOf_dvd_of_pow_eq_one h1)
    exact ⟨f, hf⟩
  have hzx' : Commute ⁅MulAut.conj g x, MulAut.conj g y⁆ (MulAut.conj g x) := by
    rw [← map_commutatorElement]
    exact hzx.map _
  have hzy' : Commute ⁅MulAut.conj g x, MulAut.conj g y⁆ (MulAut.conj g y) := by
    rw [← map_commutatorElement]
    exact hzy.map _
  obtain ⟨x'', y'', hx'', hy'', hx5'', hy5'', hcx'', hcy''⟩ := exists_lift_of_cubic hker
    (x := MulAut.conj g x) (y := MulAut.conj g y) (h := MulAut.conj g h)
    (by rw [← map_pow, hx5, map_one]) (by rw [← map_pow, hy5, map_one]) hzx' hzy'
    (by rw [← map_inv, ← map_mul, ← map_mul, hhx, map_pow])
    (by rw [← map_inv, ← map_mul, ← map_mul, hhy, map_pow])
    (by rw [← map_commutatorElement, ← map_inv, ← map_mul, ← map_mul, hhz, map_pow])
    hx hy hh (hord x' hx'P) (hord y' hy'P)
  set C := Subgroup.closure ({x'', y''} : Set Γ) with hCdef
  have hCle : Nat.card C ≤ 5 ^ 3 := by
    have hxC : x'' ∈ C := Subgroup.subset_closure (by simp)
    have hyC : y'' ∈ C := Subgroup.subset_closure (by simp)
    have hzC : ⁅x'', y''⁆ ∈ C := by
      rw [commutatorElement_def]
      exact C.mul_mem (C.mul_mem (C.mul_mem hxC hyC) (C.inv_mem hxC)) (C.inv_mem hyC)
    let F : Fin 5 × Fin 5 × Fin 5 → C := fun t =>
      ⟨x'' ^ (t.1 : ℕ) * y'' ^ (t.2.1 : ℕ) * ⁅x'', y''⁆ ^ (t.2.2 : ℕ),
        C.mul_mem (C.mul_mem (C.pow_mem hxC _) (C.pow_mem hyC _)) (C.pow_mem hzC _)⟩
    have hF : Function.Surjective F := by
      intro c
      obtain ⟨i, j, k, hi, hj, hk, hc⟩ := CFSG.SectionRank.LocalWitness.mem_closure_normalForm
        (by norm_num) hx5'' hy5'' hcx'' hcy'' c.2
      exact ⟨(⟨i, hi⟩, ⟨j, hj⟩, ⟨k, hk⟩), Subtype.ext hc.symm⟩
    calc Nat.card C ≤ Nat.card (Fin 5 × Fin 5 × Fin 5) := Nat.card_le_card_of_surjective F hF
      _ = 5 ^ 3 := by simp
  have hCmap : C.map φ = Subgroup.closure ({MulAut.conj g x, MulAut.conj g y} : Set T) := by
    rw [hCdef, MonoidHom.map_closure, Set.image_pair, hx'', hy'']
  have hCmapcard : Nat.card (C.map φ) = 5 ^ 3 := by
    rw [hCmap, ← map_conj_closure_pair,
      Subgroup.card_map_of_injective (f := (MulAut.conj g).toMonoidHom) (MulEquiv.injective _),
      hcard]
  have hrange : (φ.comp C.subtype).range = C.map φ := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hsurj : Function.Surjective (φ.comp C.subtype).rangeRestrict :=
    MonoidHom.rangeRestrict_surjective _
  have hcardeq : Nat.card C = Nat.card (φ.comp C.subtype).range := by
    refine le_antisymm ?_ (Nat.card_le_card_of_surjective _ hsurj)
    rw [hrange, hCmapcard]
    exact hCle
  have hbij := (Nat.bijective_iff_surjective_and_card _).mpr ⟨hsurj, hcardeq⟩
  have hinj : Function.Injective (φ.comp C.subtype) := fun a b hab => hbij.1 (Subtype.ext hab)
  refine ⟨C, ?_, ?_⟩
  · rw [eq_bot_iff]
    rintro c ⟨hcC, hck⟩
    have h1 : (⟨c, hcC⟩ : C) = 1 := hinj (by
      rw [map_one]
      exact MonoidHom.mem_ker.mp hck)
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val h1)
  · rw [hcardeq, hrange, hCmapcard, hT]

end CentralExt

end CFSG.AGLEmbeddingD2.CentralExt
