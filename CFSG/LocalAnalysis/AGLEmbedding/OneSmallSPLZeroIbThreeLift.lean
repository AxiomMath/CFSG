module

public import CFSG.Quasithin.Background.A3ComponentsBasic
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin

section General

variable {Y : Type*} [Group Y] [Finite Y]

theorem mem_perfectCore_of_pow_eq_one {W L : Type*} [Group W] [Finite W] [Group L] [Finite L]
    {p : ℕ} (φ : W →* L) (hφ : Function.Surjective φ) (hL : Group.IsPerfect L)
    (hker : ∀ w : W, φ w = 1 → Nat.Coprime p (orderOf w)) {w : W} {k : ℕ}
    (hwk : w ^ p ^ k = 1) : w ∈ perfectCore (⊤ : Subgroup W) := by
  set D := perfectCore (⊤ : Subgroup W)
  have hDφ : D.map φ = ⊤ := by
    rw [map_perfectCore, Subgroup.map_top_of_surjective φ hφ]
    exact perfectCore_eq_self_of_perfect (by rw [← commutator_def]; exact hL.commutator_eq_top)
  have hDn : D.Normal := by
    apply Subgroup.normalizer_eq_top_iff.mp
    refine top_le_iff.mp (le_trans ?_ (normalizer_le_normalizer_perfectCore ⊤))
    rw [Subgroup.normalizer_eq_top (H := (⊤ : Subgroup W))]
  obtain ⟨d, hdD, hdw⟩ : φ w ∈ D.map φ := hDφ ▸ Subgroup.mem_top _
  set n := d⁻¹ * w with hn
  have hn1 : φ n = 1 := by rw [hn, map_mul, map_inv, hdw, inv_mul_cancel]
  have hnc := hker n hn1
  set q := QuotientGroup.mk' D
  have hqd : q d = 1 := (QuotientGroup.eq_one_iff d).mpr hdD
  have hqw : q w = q n := by
    rw [hn, map_mul, map_inv, hqd, inv_one, one_mul]
  have h1 : orderOf (q w) ∣ p ^ k := orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hwk, map_one])
  have h2 : orderOf (q w) ∣ orderOf n := hqw ▸ orderOf_map_dvd q n
  have h3 : orderOf (q w) = 1 :=
    Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h1 (Nat.Coprime.pow_left k hnc)) h2
  rw [orderOf_eq_one_iff] at h3
  exact (QuotientGroup.eq_one_iff w).mp h3

theorem exists_mul_mem_normalizer_sylow_of_mem_normalizer {p : ℕ} [Fact p.Prime]
    {U : Subgroup Y} (P : Sylow p U) {g : Y} (hg : g ∈ Subgroup.normalizer (U : Set Y)) :
    ∃ u ∈ U, u * g ∈
      Subgroup.normalizer ((((P : Subgroup U).map U.subtype : Subgroup Y)) : Set Y) := by
  set σ : MulAut U := U.normalizerMonoidHom ⟨g, hg⟩ with hσ
  obtain ⟨u, hu⟩ := MulAction.exists_smul_eq U (σ • P) P
  refine ⟨u, u.2, Subgroup.mem_normalizer_fintype fun x hx => ?_⟩
  obtain ⟨y, hyP, rfl⟩ := hx
  have hσy : (σ y : Y) = g * y * g⁻¹ := rfl
  have h1 : σ y ∈ ((σ • P : Sylow p U) : Subgroup U) := by
    rw [Sylow.pointwise_smul_def]
    exact ⟨y, hyP, rfl⟩
  have h2 : u * σ y * u⁻¹ ∈ ((u • (σ • P) : Sylow p U) : Subgroup U) := by
    rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    exact ⟨σ y, h1, rfl⟩
  rw [hu] at h2
  refine ⟨u * σ y * u⁻¹, h2, ?_⟩
  simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv, hσy, mul_inv_rev]
  group

omit [Finite Y] in
theorem eq_one_of_mk_eq_one_of_coprime {p : ℕ} (N : Subgroup Y) [N.Normal]
    (hN : p.Coprime (Nat.card N)) {a : Y} {k : ℕ} (hak : a ^ p ^ k = 1)
    (ha : QuotientGroup.mk' N a = 1) : a = 1 := by
  have haN : a ∈ N := (QuotientGroup.eq_one_iff a).mp ha
  have h1 : orderOf a ∣ Nat.card N := Subgroup.orderOf_dvd_natCard N haN
  have h2 : orderOf a ∣ p ^ k := orderOf_dvd_of_pow_eq_one hak
  have h3 : orderOf a = 1 :=
    Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h2 (Nat.Coprime.pow_left k hN)) h1
  exact orderOf_eq_one_iff.mp h3

end General

theorem conj_pow_mul_eq {Y : Type*} [Group Y] {U : Subgroup Y}
    (hU : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a) {g v : Y}
    (hg : g ∈ Subgroup.normalizer (U : Set Y)) (hv : v ∈ U) (k : ℕ) :
    ∀ y ∈ U, (v * g) ^ k * y * ((v * g) ^ k)⁻¹ = g ^ k * y * (g ^ k)⁻¹ := by
  induction k with
  | zero => intro y _; simp
  | succ k ih =>
    intro y hy
    have h1 : g ^ k * y * (g ^ k)⁻¹ ∈ U :=
      (Subgroup.mem_normalizer_iff.mp (Subgroup.pow_mem _ hg k) y).mp hy
    have h2 : g * (g ^ k * y * (g ^ k)⁻¹) * g⁻¹ ∈ U :=
      (Subgroup.mem_normalizer_iff.mp hg _).mp h1
    calc (v * g) ^ (k + 1) * y * ((v * g) ^ (k + 1))⁻¹
        = v * (g * ((v * g) ^ k * y * ((v * g) ^ k)⁻¹) * g⁻¹) * v⁻¹ := by
          rw [pow_succ', mul_inv_rev, mul_inv_rev]; simp only [mul_assoc]
      _ = v * (g * (g ^ k * y * (g ^ k)⁻¹) * g⁻¹) * v⁻¹ := by rw [ih y hy]
      _ = g * (g ^ k * y * (g ^ k)⁻¹) * g⁻¹ := by
          rw [hU v hv _ h2, mul_assoc, mul_inv_cancel, mul_one]
      _ = g ^ (k + 1) * y * (g ^ (k + 1))⁻¹ := by
          rw [pow_succ', mul_inv_rev]; simp only [mul_assoc]

section Transport

variable {Y₁ Y₂ : Type*} [Group Y₁] [Group Y₂] [Finite Y₁] [Finite Y₂]

omit [Finite Y₂] in
theorem relIndex_map_of_injOn (θ : Y₁ →* Y₂) {A₁ F : Subgroup Y₁} (hFA : F ≤ A₁)
    (hinj : ∀ a ∈ A₁, θ a = 1 → a = 1) : (F.map θ).relIndex (A₁.map θ) = F.relIndex A₁ := by
  have hθ' : Function.Injective (θ.comp A₁.subtype) := by
    rw [injective_iff_map_eq_one]
    intro a ha
    exact Subtype.ext (hinj a a.2 ha)
  have hcard : ∀ B : Subgroup Y₁, B ≤ A₁ → Nat.card (B.map θ) = Nat.card B := by
    intro B hB
    have h1 : B.map θ = (B.subgroupOf A₁).map (θ.comp A₁.subtype) := by
      rw [← Subgroup.map_map, Subgroup.map_subgroupOf_eq_of_le hB]
    rw [h1, Subgroup.card_map_of_injective hθ',
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hB).toEquiv]
  have hle : F.map θ ≤ A₁.map θ := Subgroup.map_mono hFA
  have e1 := Subgroup.relIndex_mul_card (H := F) (K := A₁)
  have e2 := Subgroup.relIndex_mul_card (H := F.map θ) (K := A₁.map θ)
  rw [inf_of_le_left hFA] at e1
  rw [inf_of_le_left hle, hcard F hFA, hcard A₁ le_rfl] at e2
  have hpos : 0 < Nat.card F := Nat.card_pos
  exact Nat.eq_of_mul_eq_mul_right hpos (e2.trans e1.symm)

theorem scalar_pull (θ : Y₁ →* Y₂) {A₁ : Subgroup Y₁} {A₂ : Subgroup Y₂} (hA : A₁.map θ = A₂)
    (hinj : ∀ a ∈ A₁, θ a = 1 → a = 1) {t₁ : Y₁} {t₂ : Y₂}
    (ht₁ : t₁ ∈ Subgroup.normalizer (A₁ : Set Y₁))
    (hθt : ∀ k : ℕ, ∀ a ∈ A₁, θ (t₁ ^ k * a * (t₁ ^ k)⁻¹) = t₂ ^ k * θ a * (t₂ ^ k)⁻¹)
    {p m lam : ℕ} (hscal : ∀ a ∈ A₂, t₂ ^ m * a * (t₂ ^ m)⁻¹ = a ^ lam)
    (horb : ∀ k, 0 < k → k < m → ∀ F : Subgroup Y₂, F ≤ A₂ → F.relIndex A₂ = p →
      t₂ ^ k ∉ Subgroup.normalizer (F : Set Y₂)) :
    (∀ a ∈ A₁, t₁ ^ m * a * (t₁ ^ m)⁻¹ = a ^ lam) ∧
      ∀ k, 0 < k → k < m → ∀ F : Subgroup Y₁, F ≤ A₁ → F.relIndex A₁ = p →
        t₁ ^ k ∉ Subgroup.normalizer (F : Set Y₁) := by
  have hinj' : ∀ a ∈ A₁, ∀ b ∈ A₁, θ a = θ b → a = b := by
    intro a ha b hb hab
    have := hinj (a * b⁻¹) (A₁.mul_mem ha (A₁.inv_mem hb)) (by rw [map_mul, map_inv, hab,
      mul_inv_cancel])
    exact mul_inv_eq_one.mp this
  refine ⟨fun a ha => ?_, fun k hk0 hkm F hFA hF htk => ?_⟩
  · have h1 : t₁ ^ m * a * (t₁ ^ m)⁻¹ ∈ A₁ :=
      (Subgroup.mem_normalizer_iff.mp (Subgroup.pow_mem _ ht₁ m) a).mp ha
    refine hinj' _ h1 _ (A₁.pow_mem ha lam) ?_
    rw [hθt m a ha, hscal (θ a) (hA ▸ Subgroup.mem_map_of_mem θ ha), map_pow]
  · refine horb k hk0 hkm (F.map θ) (hA ▸ Subgroup.map_mono hFA) ?_ ?_
    · rw [← hA, relIndex_map_of_injOn θ hFA hinj, hF]
    · refine Subgroup.mem_normalizer_fintype fun y hy => ?_
      obtain ⟨f, hf, rfl⟩ := hy
      rw [← hθt k f (hFA hf)]
      exact Subgroup.mem_map_of_mem θ ((Subgroup.mem_normalizer_iff.mp htk f).mp hf)

omit [Finite Y₂] in
theorem scalar_push (θ : Y₁ →* Y₂) {A₁ : Subgroup Y₁} {A₂ : Subgroup Y₂} (hA : A₁.map θ = A₂)
    (hinj : ∀ a ∈ A₁, θ a = 1 → a = 1) {t₁ : Y₁} {t₂ : Y₂}
    (ht₁ : t₁ ∈ Subgroup.normalizer (A₁ : Set Y₁))
    (hθt : ∀ k : ℕ, ∀ a ∈ A₁, θ (t₁ ^ k * a * (t₁ ^ k)⁻¹) = t₂ ^ k * θ a * (t₂ ^ k)⁻¹)
    {p m lam : ℕ} (hscal : ∀ a ∈ A₁, t₁ ^ m * a * (t₁ ^ m)⁻¹ = a ^ lam)
    (horb : ∀ k, 0 < k → k < m → ∀ F : Subgroup Y₁, F ≤ A₁ → F.relIndex A₁ = p →
      t₁ ^ k ∉ Subgroup.normalizer (F : Set Y₁)) :
    (∀ a ∈ A₂, t₂ ^ m * a * (t₂ ^ m)⁻¹ = a ^ lam) ∧
      ∀ k, 0 < k → k < m → ∀ F : Subgroup Y₂, F ≤ A₂ → F.relIndex A₂ = p →
        t₂ ^ k ∉ Subgroup.normalizer (F : Set Y₂) := by
  refine ⟨fun a ha => ?_, fun k hk0 hkm F hFA hF htk => ?_⟩
  · rw [← hA] at ha
    obtain ⟨b, hb, rfl⟩ := ha
    rw [← hθt m b hb, hscal b hb, map_pow]
  · set F₁ : Subgroup Y₁ := A₁ ⊓ F.comap θ with hF₁
    have hF₁A : F₁ ≤ A₁ := inf_le_left
    have hmap : F₁.map θ = F := by
      refine le_antisymm (Subgroup.map_le_iff_le_comap.mpr inf_le_right) fun y hy => ?_
      have hy' : y ∈ A₁.map θ := hA ▸ hFA hy
      obtain ⟨b, hb, rfl⟩ := hy'
      exact ⟨b, ⟨hb, hy⟩, rfl⟩
    refine horb k hk0 hkm F₁ hF₁A ?_ ?_
    · rw [← relIndex_map_of_injOn θ hF₁A hinj, hmap, hA, hF]
    · refine Subgroup.mem_normalizer_fintype fun b hb => ⟨?_, ?_⟩
      · exact (Subgroup.mem_normalizer_iff.mp (Subgroup.pow_mem _ ht₁ k) b).mp hb.1
      · change θ (t₁ ^ k * b * (t₁ ^ k)⁻¹) ∈ F
        rw [hθt k b hb.1]
        exact (Subgroup.mem_normalizer_iff.mp htk (θ b)).mp hb.2

omit [Finite Y₁] [Finite Y₂] in
theorem isElemAbelian_of_map_injOn (θ : Y₁ →* Y₂) {A₁ : Subgroup Y₁} {p : ℕ}
    (hinj : ∀ a ∈ A₁, θ a = 1 → a = 1) (hA : IsElemAbelian p (A₁.map θ)) :
    IsElemAbelian p A₁ := by
  have hinj' : ∀ a ∈ A₁, ∀ b ∈ A₁, θ a = θ b → a = b := by
    intro a ha b hb hab
    have := hinj (a * b⁻¹) (A₁.mul_mem ha (A₁.inv_mem hb)) (by rw [map_mul, map_inv, hab,
      mul_inv_cancel])
    exact mul_inv_eq_one.mp this
  refine ⟨IsMulCommutative.of_comm fun x y => Subtype.ext ?_, fun x hx => ?_⟩
  · refine hinj' _ (A₁.mul_mem x.2 y.2) _ (A₁.mul_mem y.2 x.2) ?_
    have h := congrArg Subtype.val ((isMulCommutative_iff.mp hA.1)
      ⟨θ x, Subgroup.mem_map_of_mem θ x.2⟩ ⟨θ y, Subgroup.mem_map_of_mem θ y.2⟩)
    simp only [Subgroup.coe_mul] at h
    rw [Subgroup.coe_mul, map_mul, map_mul]
    exact h
  · refine hinj' _ (A₁.pow_mem hx p) _ A₁.one_mem ?_
    rw [map_pow, map_one]
    exact hA.2 _ (Subgroup.mem_map_of_mem θ hx)

omit [Finite Y₁] [Finite Y₂] in
theorem isElemAbelian_map_of_isElemAbelian (θ : Y₁ →* Y₂) {A₁ : Subgroup Y₁} {p : ℕ}
    (hA : IsElemAbelian p A₁) : IsElemAbelian p (A₁.map θ) := CFSG.Open.IsElemAbelian.map hA _

end Transport

theorem exists_lift_scalar {C : Type*} [Group C] [Finite C] {p : ℕ} [Fact p.Prime]
    (O : Subgroup C) [O.Normal] (hO : p.Coprime (Nat.card O)) {U : Subgroup (C ⧸ O)}
    (hU : IsElemAbelian p U) {Z : Subgroup C} (hZp : IsPGroup p Z)
    (hZU : Z ≤ U.comap (QuotientGroup.mk' O)) {c : C}
    (hcU : QuotientGroup.mk' O c ∈ Subgroup.normalizer (U : Set (C ⧸ O))) {m lam : ℕ}
    (hscal : ∀ a ∈ U, QuotientGroup.mk' O c ^ m * a * (QuotientGroup.mk' O c ^ m)⁻¹ = a ^ lam)
    (horb : ∀ k, 0 < k → k < m → ∀ F : Subgroup (C ⧸ O), F ≤ U → F.relIndex U = p →
      QuotientGroup.mk' O c ^ k ∉ Subgroup.normalizer (F : Set (C ⧸ O))) :
    ∃ A : Subgroup C, A ≤ U.comap (QuotientGroup.mk' O) ∧ IsElemAbelian p A ∧ Z ≤ A ∧
      ∃ u ∈ U.comap (QuotientGroup.mk' O), u * c ∈ Subgroup.normalizer (A : Set C) ∧
        (∀ a ∈ A, (u * c) ^ m * a * ((u * c) ^ m)⁻¹ = a ^ lam) ∧
        ∀ k, 0 < k → k < m → ∀ F : Subgroup C, F ≤ A → F.relIndex A = p →
          (u * c) ^ k ∉ Subgroup.normalizer (F : Set C) := by
  set ρ := QuotientGroup.mk' O with hρ
  set Uh : Subgroup C := U.comap ρ with hUh
  have hUcomm : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val ((isMulCommutative_iff.mp hU.1) ⟨a, ha⟩ ⟨b, hb⟩)
  have hcN : c ∈ Subgroup.normalizer (Uh : Set C) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    change ρ y ∈ U ↔ ρ (c * y * c⁻¹) ∈ U
    rw [map_mul, map_mul, map_inv]
    exact Subgroup.mem_normalizer_iff.mp hcU (ρ y)
  have hZp' : IsPGroup p (Z.subgroupOf Uh) := hZp.comap_subtype
  obtain ⟨A₀, hA₀⟩ := hZp'.exists_le_sylow
  obtain ⟨u, huUh, hucN⟩ := exists_mul_mem_normalizer_sylow_of_mem_normalizer A₀ hcN
  set A : Subgroup C := (A₀ : Subgroup Uh).map Uh.subtype with hA
  have hAUh : A ≤ Uh := Subgroup.map_subtype_le _
  have hAp : IsPGroup p A := A₀.isPGroup'.map _
  have hinj : ∀ a ∈ A, ρ a = 1 → a = 1 := by
    intro a ha h1
    obtain ⟨k, hk⟩ := hAp ⟨a, ha⟩
    exact eq_one_of_mk_eq_one_of_coprime O hO (k := k)
      (by simpa using congrArg Subtype.val hk) h1
  set ρU : Uh →* U := (ρ.comp Uh.subtype).codRestrict U (fun y => y.2) with hρU
  have hρUs : Function.Surjective ρU := by
    intro v
    obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective O (v : C ⧸ O)
    have hyU : y ∈ Uh := by
      change ρ y ∈ U
      rw [hρ, hy]
      exact v.2
    exact ⟨⟨y, hyU⟩, Subtype.ext hy⟩
  have hUtop : IsPGroup p (⊤ : Subgroup U) := fun g =>
    ⟨1, Subtype.ext (Subtype.ext (by simpa using hU.2 _ (g : U).2))⟩
  have hAU : A.map ρ = U := by
    have h1 := (A₀.mapSurjective hρUs).is_maximal' hUtop le_top
    rw [Sylow.coe_mapSurjective] at h1
    refine le_antisymm ?_ fun v hv => ?_
    · rintro _ ⟨a, ha, rfl⟩
      exact hAUh ha
    · have hv' : (⟨v, hv⟩ : U) ∈ (A₀ : Subgroup Uh).map ρU := h1 ▸ Subgroup.mem_top _
      obtain ⟨a, ha, hav⟩ := hv'
      exact ⟨(a : C), ⟨a, ha, rfl⟩, congrArg Subtype.val hav⟩
  have hAel : IsElemAbelian p A := isElemAbelian_of_map_injOn ρ hinj (hAU ▸ hU)
  have hθρ : ∀ k : ℕ, ∀ a ∈ A, ρ ((u * c) ^ k * a * ((u * c) ^ k)⁻¹) =
      ρ c ^ k * ρ a * (ρ c ^ k)⁻¹ := by
    intro k a ha
    rw [map_mul, map_mul, map_inv, map_pow, map_mul]
    exact conj_pow_mul_eq hUcomm hcU huUh k (ρ a) (hAUh ha)
  obtain ⟨hscalA, horbA⟩ := scalar_pull ρ hAU hinj hucN hθρ hscal horb
  refine ⟨A, hAUh, hAel, fun x hx => ?_, u, huUh, hucN, hscalA, horbA⟩
  exact ⟨⟨x, hZU hx⟩, hA₀ hx, rfl⟩

end CFSG.AGLEmbedding
