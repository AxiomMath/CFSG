module

public import CFSG.GH74.Generic.Certificates

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec5.Rank5

open Subgroup
open scoped commutatorElement

theorem aut_pow_six {Q : Type*} [Group Q] [Finite Q] (hQ : Nat.card Q = 4) (σ : MulAut Q) :
    σ ^ 6 = 1 := by
  classical
  have : Fintype Q := Fintype.ofFinite Q
  have hcard : Fintype.card Q = 4 := by rw [← Nat.card_eq_fintype_card]; exact hQ
  have hT : Fintype.card {q : Q // q ≠ 1} = 3 := by
    rw [Fintype.card_subtype_compl]
    have hone : Fintype.card {q : Q // q = 1} = 1 := by simp
    rw [hone, hcard]
  let f : MulAut Q →* Equiv.Perm {q : Q // q ≠ 1} :=
    { toFun := fun a => Equiv.Perm.subtypePerm a.toEquiv (by intro v; simp)
      map_one' := by ext v; rfl
      map_mul' := by intro a b; ext v; rfl }
  have hf : Function.Injective f := by
    intro a b hab
    ext v
    by_cases hv : v = 1
    · simp [hv]
    · exact congrArg Subtype.val (DFunLike.congr_fun hab ⟨v, hv⟩)
  apply hf
  rw [map_pow, map_one]
  have h6 : Nat.card (Equiv.Perm {q : Q // q ≠ 1}) = 6 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, hT]; rfl
  rw [← h6]
  exact pow_card_eq_one'

theorem pow_two_of_pow_two_pow {M : Type*} [Monoid M] {σ : M} (h6 : σ ^ 6 = 1) {k : ℕ}
    (hk : σ ^ (2 ^ k) = 1) : σ ^ 2 = 1 := by
  cases k with
  | zero =>
    have : σ = 1 := by simpa using hk
    rw [this, one_pow]
  | succ k =>
    have h1 : σ ^ (Nat.gcd 6 (2 ^ (k + 1))) = 1 := pow_gcd_eq_one.2 ⟨h6, hk⟩
    have hg : Nat.gcd 6 (2 ^ (k + 1)) = 2 := by
      have e : (6 : ℕ) = 2 * 3 := by norm_num
      have e2 : (2 : ℕ) ^ (k + 1) = 2 * 2 ^ k := by ring
      rw [e, e2, Nat.gcd_mul_left]
      have : Nat.Coprime 3 (2 ^ k) := Nat.Coprime.pow_right k (by norm_num)
      rw [this.gcd_eq_one]
    rwa [hg] at h1

theorem sq_acts_trivially {P V Γ : Type*} [Group P] [Group V] [Finite V] [Group Γ]
    (hV : Nat.card V = 4) (ρ : Γ →* MulAut P) (β : P →* V) (hβ : Function.Surjective β)
    (hker : ∀ (γ : Γ) (g : P), β g = 1 → β (ρ γ g) = 1) {γ : Γ} {k : ℕ} (hγ : γ ^ (2 ^ k) = 1)
    (g : P) : β (ρ (γ ^ 2) g) = β g := by
  classical
  have hker' : ∀ γ : Γ, β.ker ≤ (β.comp (ρ γ).toMonoidHom).ker := fun γ x hx =>
    MonoidHom.mem_ker.2 (hker γ x (MonoidHom.mem_ker.1 hx))
  let ind : Γ → (V →* V) := fun γ =>
    (MonoidHom.liftOfSurjective β hβ) ⟨β.comp (ρ γ).toMonoidHom, hker' γ⟩
  have hind : ∀ γ g, ind γ (β g) = β (ρ γ g) := fun γ g => by simp [ind]
  have hbij : ∀ γ, Function.Bijective (ind γ) := by
    intro γ
    constructor
    · rw [injective_iff_map_eq_one]
      intro v hv
      obtain ⟨g, rfl⟩ := hβ v
      rw [hind] at hv
      have := hker γ⁻¹ _ hv
      simpa using this
    · intro v
      obtain ⟨g, rfl⟩ := hβ v
      exact ⟨β (ρ γ⁻¹ g), by rw [hind]; simp⟩
  let act : Γ →* MulAut V :=
    { toFun := fun γ => MulEquiv.ofBijective (ind γ) (hbij γ)
      map_one' := by
        ext v
        obtain ⟨g, rfl⟩ := hβ v
        show ind 1 (β g) = β g
        rw [hind]; simp
      map_mul' := by
        intro γ δ
        ext v
        obtain ⟨g, rfl⟩ := hβ v
        show ind (γ * δ) (β g) = ind γ (ind δ (β g))
        rw [hind, hind, hind]
        simp }
  have hact : ∀ γ g, act γ (β g) = β (ρ γ g) := fun γ g => hind γ g
  have h1 : (act γ) ^ (2 ^ k) = 1 := by rw [← map_pow, hγ, map_one]
  have h2 : (act γ) ^ 2 = 1 := pow_two_of_pow_two_pow (aut_pow_six hV _) h1
  have h3 : act (γ ^ 2) = 1 := by rw [map_pow, h2]
  calc β (ρ (γ ^ 2) g) = act (γ ^ 2) (β g) := (hact _ _).symm
    _ = β g := by rw [h3]; rfl

theorem exists_sq_of_sq_eq_one {Q : Type*} [Group Q] [Finite Q] (hp : IsPGroup 2 Q)
    (h4 : 4 ≤ Nat.card Q) {g : Q} (hg : ∀ x, x ∈ Subgroup.zpowers g) {x : Q} (hx : x * x = 1) :
    ∃ y : Q, y * y = x := by
  obtain ⟨t, ht⟩ := hp.exists_card_eq
  have hord : orderOf g = 2 ^ t := by rw [orderOf_eq_card_of_forall_mem_zpowers hg, ht]
  have ht2 : 2 ≤ t := by
    by_contra hlt
    have : t ≤ 1 := by omega
    have h2 : 2 ^ t ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) this
    rw [ht] at h4
    omega
  obtain ⟨s, rfl⟩ := Subgroup.mem_zpowers_iff.1 (hg x)
  have h1 : g ^ (2 * s) = 1 := by
    rw [two_mul, zpow_add]
    simpa [mul_zpow_self] using hx
  have h2 : ((orderOf g : ℕ) : ℤ) ∣ 2 * s := orderOf_dvd_iff_zpow_eq_one.2 h1
  rw [hord] at h2
  obtain ⟨u, rfl⟩ : ∃ u, t = u + 1 := ⟨t - 1, by omega⟩
  have h3 : ((2 ^ u : ℕ) : ℤ) ∣ s := by
    have : ((2 : ℤ) * (2 ^ u : ℕ)) ∣ 2 * s := by
      push_cast at h2 ⊢
      rw [pow_succ] at h2
      rwa [mul_comm] at h2
    exact Int.dvd_of_mul_dvd_mul_left (by norm_num) this
  have h4 : (2 : ℤ) ∣ s := by
    obtain ⟨u', rfl⟩ : ∃ u', u = u' + 1 := ⟨u - 1, by omega⟩
    exact dvd_trans (by norm_num [pow_succ]) h3
  obtain ⟨s', rfl⟩ := h4
  exact ⟨g ^ s', by rw [← zpow_add, ← two_mul]⟩

theorem exists_sq_mul_of_cyclic {G : Type} [Group G] [Finite G] {A P : Subgroup G} (hPA : P ≤ A)
    (hAnorm : A ≤ normalizer (P : Set G)) {c : G} (hc : c ∈ A) (hAc : A = P ⊔ zpowers c)
    (hp : IsPGroup 2 ↥A) (h4 : 4 ≤ P.relIndex A) {a : G} (ha : a ∈ A) (ha2 : a * a = 1) :
    ∃ d ∈ A, ∃ q ∈ P, a = d * d * q := by
  have : (P.subgroupOf A).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hPA).2 hAnorm
  let Q := ↥A ⧸ P.subgroupOf A
  have hcard : 4 ≤ Nat.card Q := by
    have : P.relIndex A = Nat.card Q := Subgroup.index_eq_card _
    omega
  have hpQ : IsPGroup 2 Q := hp.to_quotient (P.subgroupOf A)
  let g : Q := QuotientGroup.mk ⟨c, hc⟩
  have hg : ∀ x : Q, x ∈ Subgroup.zpowers g := by
    intro x
    obtain ⟨⟨y, hy⟩, rfl⟩ := QuotientGroup.mk_surjective x
    have hczp : zpowers c ≤ normalizer (P : Set G) := (zpowers_le).2 (hAnorm hc)
    have hset := Subgroup.coe_mul_of_left_le_normalizer_right (zpowers c) P hczp
    have hy' : y ∈ (↑(zpowers c ⊔ P) : Set G) := by rw [sup_comm, ← hAc]; exact hy
    rw [hset] at hy'
    obtain ⟨u, hu, v, hv, rfl⟩ := Set.mem_mul.1 hy'
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hu
    refine Subgroup.mem_zpowers_iff.2 ⟨n, ?_⟩
    have hv1 : (QuotientGroup.mk (⟨v, hPA hv⟩ : ↥A) : Q) = 1 := by
      rw [QuotientGroup.eq_one_iff]
      exact hv
    have : (⟨c ^ n * v, hy⟩ : ↥A) = (⟨c, hc⟩ : ↥A) ^ n * ⟨v, hPA hv⟩ := by
      apply Subtype.ext; simp
    rw [this, QuotientGroup.mk_mul, hv1, mul_one]
    simp [g]
  have hxx : (QuotientGroup.mk (⟨a, ha⟩ : ↥A) : Q) * QuotientGroup.mk ⟨a, ha⟩ = 1 := by
    rw [← QuotientGroup.mk_mul]
    have : (⟨a, ha⟩ : ↥A) * ⟨a, ha⟩ = 1 := Subtype.ext ha2
    rw [this]; exact QuotientGroup.mk_one _
  obtain ⟨y, hy⟩ := exists_sq_of_sq_eq_one hpQ hcard hg hxx
  obtain ⟨⟨d, hd⟩, rfl⟩ := QuotientGroup.mk_surjective y
  refine ⟨d, hd, (d * d)⁻¹ * a, ?_, by group⟩
  rw [← QuotientGroup.mk_mul, QuotientGroup.eq] at hy
  exact hy

theorem rankCertified_four_of_frattini_section {G : Type} [Group G] [Finite G]
    (P : Subgroup G) (a : G) (ha : a ∈ Subgroup.normalizer (P : Set G)) (ha2 : a * a = 1)
    (haP : a ∉ P) {W : Type} [CommGroup W] (hW : ∀ w : W, w * w = 1)
    (β : ↥P →* W) (e : Fin 4 → ↥P)
    (hind : ∀ c : Fin 4 → Fin 2, c ≠ 0 → (List.ofFn fun i => β (e i) ^ (c i : ℕ)).prod ≠ 1)
    (hact : ∀ g : ↥P, β ((P.normalizerMonoidHom ⟨a, ha⟩) g) = β g) :
    CFSG.GH74.Generic.RankCertified G 4 := by
  classical
  let N : Subgroup G := (β.ker).map P.subtype
  have memN : ∀ g : G, g ∈ N ↔ ∃ h : g ∈ P, β ⟨g, h⟩ = 1 := by
    intro g
    constructor
    · rintro ⟨n, hn, rfl⟩
      exact ⟨n.2, by simpa using hn⟩
    · rintro ⟨h, hg⟩
      exact ⟨⟨g, h⟩, hg, rfl⟩
  have hNP : N ≤ P := fun g hg => ((memN g).1 hg).1
  have hPconj : ∀ (g : ↥P) (n : G), n ∈ N → (g : G) * n * (g : G)⁻¹ ∈ N := by
    intro g n hn
    obtain ⟨hnP, hn1⟩ := (memN n).1 hn
    have hmem : (g : G) * n * (g : G)⁻¹ ∈ P := mul_mem (mul_mem g.2 hnP) (inv_mem g.2)
    refine (memN _).2 ⟨hmem, ?_⟩
    have : (⟨(g : G) * n * (g : G)⁻¹, hmem⟩ : ↥P) = g * ⟨n, hnP⟩ * g⁻¹ := rfl
    rw [this, map_mul, map_mul, hn1, mul_one, map_inv, mul_inv_cancel]
  have hPnorm : ∀ g : ↥P, (g : G) ∈ Subgroup.normalizer (N : Set G) := by
    intro g
    rw [Subgroup.mem_normalizer_iff]
    intro n
    constructor
    · intro hn
      exact hPconj g n hn
    · intro hn
      have := hPconj g⁻¹ _ hn
      simpa [mul_assoc] using this
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
  have haconj : ∀ n : G, n ∈ N → a * n * a⁻¹ ∈ N := by
    intro n hn
    obtain ⟨hnP, hn1⟩ := (memN n).1 hn
    have hmem : a * n * a⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.1 ha n).1 hnP
    refine (memN _).2 ⟨hmem, ?_⟩
    have : (⟨a * n * a⁻¹, hmem⟩ : ↥P) = (P.normalizerMonoidHom ⟨a, ha⟩) ⟨n, hnP⟩ := rfl
    rw [this, hact]
    exact hn1
  have hanorm : a ∈ Subgroup.normalizer (N : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro n
    constructor
    · exact haconj n
    · intro hn
      have h1 := haconj _ hn
      have e : a * (a * n * a⁻¹) * a⁻¹ = n := by
        rw [hainv]
        calc a * (a * n * a) * a = (a * a) * n * (a * a) := by group
          _ = n := by rw [ha2]; group
      rwa [e] at h1
  let xs : Fin 4 → G := fun i => (e i : G)
  let x : Fin 5 → G := Fin.snoc (α := fun _ => G) xs a
  have hxcast : ∀ i : Fin 4, x i.castSucc = (e i : G) := fun i => by
    simp only [x, xs, Fin.snoc_castSucc]
  have hxlast : x (Fin.last 4) = a := by simp only [x, Fin.snoc_last]
  have hxcases : ∀ i : Fin 5, (∃ j : Fin 4, x i = (e j : G)) ∨ x i = a := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · right; exact hxlast
    · left; exact ⟨j, hxcast j⟩
  have hnorm : ∀ i, x i ∈ Subgroup.normalizer (N : Set G) := by
    intro i
    rcases hxcases i with ⟨j, hj⟩ | hj
    · rw [hj]; exact hPnorm (e j)
    · rw [hj]; exact hanorm
  have hsq : ∀ i, x i ^ 2 ∈ N := by
    intro i
    rcases hxcases i with ⟨j, hj⟩ | hj
    · rw [hj]
      refine (memN _).2 ⟨pow_mem (e j).2 2, ?_⟩
      have : (⟨(e j : G) ^ 2, pow_mem (e j).2 2⟩ : ↥P) = e j ^ 2 := rfl
      rw [this, map_pow, pow_two]
      exact hW _
    · rw [hj, pow_two, ha2]
      exact one_mem _
  have hPP : ∀ u v : ↥P, ⁅(u : G), (v : G)⁆ ∈ N := by
    intro u v
    have hmem : ⁅(u : G), (v : G)⁆ ∈ P := (⁅u, v⁆ : ↥P).2
    refine (memN _).2 ⟨hmem, ?_⟩
    have : (⟨⁅(u : G), (v : G)⁆, hmem⟩ : ↥P) = ⁅u, v⁆ := rfl
    rw [this, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.2 (mul_comm _ _)
  have hPa : ∀ u : ↥P, ⁅(u : G), a⁆ ∈ N := by
    intro u
    have hrw : ⁅(u : G), a⁆ = (u : G) * (a * (u : G)⁻¹ * a⁻¹) := by
      simp only [commutatorElement_def]; group
    have h1 : a * (u : G)⁻¹ * a⁻¹ = (((P.normalizerMonoidHom ⟨a, ha⟩) u⁻¹ : ↥P) : G) := rfl
    have hmem : ⁅(u : G), a⁆ ∈ P := by
      rw [hrw, h1]
      exact mul_mem u.2 ((P.normalizerMonoidHom ⟨a, ha⟩) u⁻¹).2
    refine (memN _).2 ⟨hmem, ?_⟩
    have : (⟨⁅(u : G), a⁆, hmem⟩ : ↥P) = u * (P.normalizerMonoidHom ⟨a, ha⟩) u⁻¹ :=
      Subtype.ext (by rw [Subgroup.coe_mul, ← h1, ← hrw])
    rw [this, map_mul, hact, map_inv, mul_inv_cancel]
  have hcomm : ∀ i j, ⁅x i, x j⁆ ∈ N := by
    intro i j
    rcases hxcases i with ⟨i', hi⟩ | hi <;> rcases hxcases j with ⟨j', hj⟩ | hj
    · rw [hi, hj]; exact hPP _ _
    · rw [hi, hj]; exact hPa _
    · rw [hi, hj, ← commutatorElement_inv]; exact inv_mem (hPa _)
    · rw [hi, hj]; simp
  have hker : ∀ c : Fin 5 → Fin 2, c ≠ 0 →
      (List.ofFn fun i => x i ^ (c i : ℕ)).prod ∉ N := by
    intro c hc hmemN
    have hprod : (List.ofFn fun i => x i ^ (c i : ℕ)).prod =
        (((List.ofFn fun i : Fin 4 => e i ^ ((c i.castSucc : Fin 2) : ℕ)).prod : ↥P) : G) *
          a ^ ((c (Fin.last 4) : Fin 2) : ℕ) := by
      rw [List.ofFn_succ', List.prod_concat, hxlast]
      congr 1
    rw [hprod] at hmemN
    rcases (by decide : ∀ t : Fin 2, t = 0 ∨ t = 1) (c (Fin.last 4)) with h | h
    · rw [h] at hmemN
      simp only [Fin.val_zero, pow_zero, mul_one] at hmemN
      obtain ⟨hpP, hp1⟩ := (memN _).1 hmemN
      have hβp : β (List.ofFn fun i : Fin 4 => e i ^ ((c i.castSucc : Fin 2) : ℕ)).prod = 1 := hp1
      rw [map_list_prod, List.map_ofFn] at hβp
      refine hind (fun i => c i.castSucc) ?_ ?_
      · intro h0
        apply hc
        funext i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simpa using h
        · exact congrFun h0 j
      · simpa [Function.comp_def, map_pow] using hβp
    · rw [h] at hmemN
      simp only [Fin.val_one, pow_one] at hmemN
      apply haP
      generalize (List.ofFn fun i : Fin 4 => e i ^ ((c i.castSucc : Fin 2) : ℕ)).prod = p at hmemN
      have h1 := hNP hmemN
      have h2 : ((p : ↥P) : G)⁻¹ ∈ P := inv_mem p.2
      have h3 := mul_mem h2 h1
      rwa [inv_mul_cancel_left] at h3
  exact CFSG.GH74.Generic.rankCertified_of_section_involutions N x hnorm hsq hcomm hker (s := 4)
    (by norm_num)

end CFSG.GH74.GLS.Stage1.Thm3.Sec5.Rank5
