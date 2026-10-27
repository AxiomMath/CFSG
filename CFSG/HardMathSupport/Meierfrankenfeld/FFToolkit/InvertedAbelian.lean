module

public import CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.Heisenberg
public import CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.HyperplaneOrbit

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit

open CFSG.Quasithin

section Restrict

variable {W : Type} [CommGroup W] [Finite W] {C : Subgroup W}

@[expose] noncomputable def resC (C : Subgroup W) (a : MulAut W) (ha : ∀ c ∈ C, a c ∈ C) :
    MulAut ↥C :=
  MulEquiv.ofBijective
    (MonoidHom.mk' (fun c : ↥C => (⟨a (c : W), ha c c.2⟩ : ↥C))
      (fun _ _ => Subtype.ext (map_mul a _ _)))
    (Finite.injective_iff_bijective.1 fun _ _ h => Subtype.ext (a.injective (congrArg Subtype.val h)))

theorem coe_resC (a : MulAut W) (ha : ∀ c ∈ C, a c ∈ C) (c : ↥C) :
    ((resC C a ha c : ↥C) : W) = a c := rfl

theorem coe_resC_pow (a : MulAut W) (ha : ∀ c ∈ C, a c ∈ C) (n : ℕ) (c : ↥C) :
    (((resC C a ha ^ n) c : ↥C) : W) = (a ^ n) c := by
  induction n generalizing c with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', pow_succ' a, MulAut.mul_apply, MulAut.mul_apply, coe_resC, ih]

theorem mem_fixV_zpowers_iff {V : Type} [CommGroup V] {g : MulAut V} {v : V} :
    v ∈ fixV (Subgroup.zpowers g) ↔ g v = v :=
  CFSG.Quasithin.mem_fixV_zpowers_iff_apply

theorem index_fixV_resC (a : MulAut W) (ha : ∀ c ∈ C, a c ∈ C) :
    (fixV (Subgroup.zpowers (resC C a ha))).index =
      (fixV (Subgroup.zpowers a) ⊓ C).relIndex C := by
  have : fixV (Subgroup.zpowers (resC C a ha)) = (fixV (Subgroup.zpowers a) ⊓ C).subgroupOf C := by
    ext c
    rw [mem_fixV_zpowers_iff, Subgroup.mem_subgroupOf, Subgroup.mem_inf, mem_fixV_zpowers_iff]
    constructor
    · intro h
      exact ⟨congrArg Subtype.val h, c.2⟩
    · intro h
      exact Subtype.ext h.1
  rw [this]
  rfl

end Restrict

variable {W : Type} [CommGroup W] [Finite W]

theorem index_inf_le_sq_of_inverts (_hW : ∀ w : W, w * w = 1) {C : Subgroup W} {x t : MulAut W}
    (hxC : ∀ c ∈ C, x c ∈ C) (htC : ∀ c ∈ C, t c ∈ C) {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hx : x ^ p = 1) (ht : t * t = 1) (htx : t * x * t⁻¹ = x⁻¹) :
    (fixV (Subgroup.zpowers x) ⊓ C).relIndex C ≤
      ((fixV (Subgroup.zpowers t) ⊓ C).relIndex C) ^ 2 := by
  have hodd : Odd p := (Fact.out : Nat.Prime p).odd_of_ne_two hp2
  have hx' : resC C x hxC ^ p = 1 := by
    ext c
    rw [coe_resC_pow, hx]
    rfl
  have ht' : resC C t htC * resC C t htC = 1 := by
    ext c
    show t (t c) = c
    have := congrArg (fun f : MulAut W => f (c : W)) ht
    simpa using this
  have htx' : resC C t htC * resC C x hxC * (resC C t htC)⁻¹ = (resC C x hxC)⁻¹ := by
    rw [inv_eq_of_mul_eq_one_right ht']
    refine eq_inv_of_mul_eq_one_left ?_
    ext c
    show t (x (t (x c))) = c
    have ht1 : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
    rw [ht1] at htx
    have h2 : t * x * t * x = 1 := by rw [htx, inv_mul_cancel]
    have := congrArg (fun f : MulAut W => f (c : W)) h2
    simpa using this
  have key := index_fixV_le_sq_of_inverts hodd hx' ht' htx'
  rwa [index_fixV_resC, index_fixV_resC] at key

section Product

variable {ι : Type} [Fintype ι] {C : ι → Subgroup W} {K : Subgroup W}

omit [Finite W] in
theorem card_eq_prod_of_equiv (e : (∀ i, ↥(C i)) ≃* ↥K) :
    Nat.card ↥K = ∏ i, Nat.card ↥(C i) := by
  rw [← Nat.card_pi]
  exact (Nat.card_congr e.toEquiv).symm

omit [Finite W] in
theorem card_fixV_inf_eq_prod (e : (∀ i, ↥(C i)) ≃* ↥K)
    (he : ∀ f, ((e f : ↥K) : W) = ∏ i, (f i : W)) {t : MulAut W}
    (htC : ∀ i, ∀ c ∈ C i, t c ∈ C i) :
    Nat.card ↥(fixV (Subgroup.zpowers t) ⊓ K) =
      ∏ i, Nat.card ↥(fixV (Subgroup.zpowers t) ⊓ C i) := by
  classical
  have h1 : ∀ i, Nat.card ↥(fixV (Subgroup.zpowers t) ⊓ C i) =
      Nat.card {c : ↥(C i) // t (c : W) = c} := by
    intro i
    refine Nat.card_congr
      { toFun := fun c => ⟨⟨c.1, (Subgroup.mem_inf.1 c.2).2⟩,
          mem_fixV_zpowers_iff.1 (Subgroup.mem_inf.1 c.2).1⟩
        invFun := fun c => ⟨c.1.1, Subgroup.mem_inf.2
          ⟨mem_fixV_zpowers_iff.2 c.2, c.1.2⟩⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  simp_rw [h1]
  rw [← Nat.card_pi]
  have h2 := Nat.card_congr (Equiv.subtypePiEquivPi (β := fun i => ↥(C i))
    (p := fun i (c : ↥(C i)) => t (c : W) = c))
  rw [← h2]
  have htprod : ∀ f : (∀ i, ↥(C i)), t (∏ i, (f i : W)) = ∏ i, t (f i : W) := fun f =>
    map_prod t _ _
  refine Nat.card_congr (Equiv.ofBijective
    (fun f : {f : (∀ i, ↥(C i)) // ∀ i, t (f i : W) = f i} =>
      (⟨(e f.1 : W), Subgroup.mem_inf.2 ⟨mem_fixV_zpowers_iff.2 ?_, (e f.1).2⟩⟩ :
        ↥(fixV (Subgroup.zpowers t) ⊓ K))) ⟨?_, ?_⟩).symm
  · rw [he, htprod]
    exact Finset.prod_congr rfl fun i _ => f.2 i
  · intro f g h
    apply Subtype.ext
    apply e.injective
    exact Subtype.ext (congrArg (fun z : ↥(fixV (Subgroup.zpowers t) ⊓ K) => (z : W)) h)
  · rintro ⟨w, hw⟩
    obtain ⟨hwt, hwK⟩ := Subgroup.mem_inf.1 hw
    have hwt' := mem_fixV_zpowers_iff.1 hwt
    set f := e.symm ⟨w, hwK⟩ with hf
    have hef : ((e f : ↥K) : W) = w := by rw [hf, MulEquiv.apply_symm_apply]
    have hprod : ∏ i, (f i : W) = w := by rw [← he, hef]
    let f' : ∀ i, ↥(C i) := fun i => ⟨t (f i : W), htC i _ (f i).2⟩
    have hf' : e f' = e f := by
      apply Subtype.ext
      rw [he, hef]
      show ∏ i, t (f i : W) = w
      rw [← htprod, hprod, hwt']
    have hff : f' = f := e.injective hf'
    refine ⟨⟨f, fun i => ?_⟩, Subtype.ext hef⟩
    exact congrArg (fun g : ∀ i, ↥(C i) => ((g i : ↥(C i)) : W)) hff

end Product

section Decomp

variable {ι : Type} [Fintype ι] {C : ι → Subgroup W} {K : Subgroup W}

theorem card_le_relIndex_sq_of_equiv (e : (∀ i, ↥(C i)) ≃* ↥K)
    (he : ∀ f, ((e f : ↥K) : W) = ∏ i, (f i : W)) {t : MulAut W}
    (htC : ∀ i, ∀ c ∈ C i, t c ∈ C i)
    (hi : ∀ i, Nat.card ↥(C i) ≤ ((fixV (Subgroup.zpowers t) ⊓ C i).relIndex (C i)) ^ 2) :
    Nat.card ↥K ≤ ((fixV (Subgroup.zpowers t) ⊓ K).relIndex K) ^ 2 := by
  set F := fixV (Subgroup.zpowers t)
  have hK := card_eq_prod_of_equiv e
  have hKt := card_fixV_inf_eq_prod e he htC
  have hrel : ∀ S : Subgroup W, (F ⊓ S).relIndex S * Nat.card ↥(F ⊓ S) = Nat.card S := by
    intro S
    have h := Subgroup.relIndex_mul_card (H := F ⊓ S) (K := S)
    rwa [inf_assoc, inf_idem] at h
  have hpos : ∀ S : Subgroup W, 0 < Nat.card ↥(F ⊓ S) := fun S => Nat.card_pos
  have hprodpos : 0 < ∏ i, Nat.card ↥(F ⊓ C i) :=
    Finset.prod_pos fun i _ => hpos (C i)
  have hJ : (F ⊓ K).relIndex K = ∏ i, (F ⊓ C i).relIndex (C i) := by
    refine Nat.eq_of_mul_eq_mul_right hprodpos ?_
    calc (F ⊓ K).relIndex K * ∏ i, Nat.card ↥(F ⊓ C i)
        = (F ⊓ K).relIndex K * Nat.card ↥(F ⊓ K) := by rw [hKt]
      _ = ∏ i, Nat.card ↥(C i) := by rw [hrel K, hK]
      _ = (∏ i, (F ⊓ C i).relIndex (C i)) * ∏ i, Nat.card ↥(F ⊓ C i) := by
        rw [← Finset.prod_mul_distrib]
        exact Finset.prod_congr rfl fun i _ => (hrel (C i)).symm
  rw [hK, hJ, ← Finset.prod_pow]
  exact Finset.prod_le_prod fun i _ => hi i

end Decomp

theorem card_le_relIndex_sq_of_inverts_of_fix_eq_bot (_hW : ∀ w : W, w * w = 1)
    {C : Subgroup W} {x t : MulAut W} (hxC : ∀ c ∈ C, x c ∈ C) (htC : ∀ c ∈ C, t c ∈ C) {p : ℕ}
    [Fact p.Prime] (hp2 : p ≠ 2) (hx : x ^ p = 1) (ht : t * t = 1) (htx : t * x * t⁻¹ = x⁻¹)
    (hfix : fixV (Subgroup.zpowers x) ⊓ C = ⊥) :
    Nat.card ↥C ≤ ((fixV (Subgroup.zpowers t) ⊓ C).relIndex C) ^ 2 := by
  have h := index_inf_le_sq_of_inverts _hW hxC htC hp2 hx ht htx
  have hc : (fixV (Subgroup.zpowers x) ⊓ C).relIndex C = Nat.card ↥C := by
    have := Subgroup.relIndex_mul_card (H := fixV (Subgroup.zpowers x) ⊓ C) (K := C)
    rw [inf_assoc, inf_idem] at this
    have h1 : Nat.card ↥(fixV (Subgroup.zpowers x) ⊓ C) = 1 := by rw [hfix]; simp
    rwa [h1, mul_one] at this
  rwa [hc] at h

section Hyperplane

theorem sup_zpowers_eq_of_relIndex_eq_prime {G : Type*} [Group G] {X D : Subgroup G} {p : ℕ}
    [Fact p.Prime] (hDX : D ≤ X) (hD : D.relIndex X = p) {x : G} (hx : x ∈ X) (hxD : x ∉ D) :
    D ⊔ Subgroup.zpowers x = X := by
  have hM : D ⊔ Subgroup.zpowers x ≤ X := sup_le hDX (Subgroup.zpowers_le.2 hx)
  have h := Subgroup.relIndex_mul_relIndex D (D ⊔ Subgroup.zpowers x) X le_sup_left hM
  rw [hD] at h
  rcases (Nat.dvd_prime (Fact.out : p.Prime)).1 (Dvd.intro _ h) with h1 | h1
  · rw [h1, one_mul] at h
    exact absurd ((Subgroup.relIndex_eq_one.1 h1) (le_sup_right (b := Subgroup.zpowers x)
      (Subgroup.mem_zpowers x))) hxD
  · rw [h1] at h
    have := Nat.eq_of_mul_eq_mul_left (Fact.out : p.Prime).pos (h.trans (mul_one p).symm)
    exact le_antisymm hM (Subgroup.relIndex_eq_one.1 this)

end Hyperplane

section HyperplaneFactor

variable {W : Type} [CommGroup W] [Finite W]

omit [Finite W] in
theorem mem_fixV_sup_zpowers {D : Subgroup (MulAut W)} {x : MulAut W} {v : W} (hD : v ∈ fixV D)
    (hx : x v = v) : v ∈ fixV (D ⊔ Subgroup.zpowers x) := by
  have : D ⊔ Subgroup.zpowers x ≤ MulAction.stabilizer (MulAut W) v :=
    sup_le (fun d hd => by rw [MulAction.mem_stabilizer_iff, MulAut.smul_def]; exact hD d hd)
      (Subgroup.zpowers_le.2 (by rw [MulAction.mem_stabilizer_iff, MulAut.smul_def]; exact hx))
  intro g hg
  have := this hg
  rwa [MulAction.mem_stabilizer_iff, MulAut.smul_def] at this

omit [Finite W] in
theorem map_mem_fixV_inf_of_inverts {X D : Subgroup (MulAut W)} {K : Subgroup W} {t : MulAut W}
    (ht : t * t = 1) (htK : ∀ k ∈ K, t k ∈ K) (htX : ∀ x ∈ X, t * x * t⁻¹ = x⁻¹)
    (hDX : D ≤ X) {c : W} (hc : c ∈ fixV D ⊓ K) : t c ∈ fixV D ⊓ K := by
  obtain ⟨hcD, hcK⟩ := Subgroup.mem_inf.1 hc
  have ht1 : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  refine Subgroup.mem_inf.2 ⟨fun d hd => ?_, htK c hcK⟩
  have h2 : d⁻¹ ∈ D := D.inv_mem hd
  have h1 : t * d⁻¹ * t⁻¹ = (d⁻¹)⁻¹ := htX d⁻¹ (hDX h2)
  rw [ht1, inv_inv] at h1
  have h3 : d * t = t * d⁻¹ := by
    calc d * t = (t * d⁻¹ * t) * t := by rw [h1]
      _ = t * d⁻¹ := by rw [mul_assoc, ht, mul_one]
  have := congrArg (fun f : MulAut W => f c) h3
  simp only [MulAut.mul_apply] at this
  rw [this, hcD _ h2]

theorem card_le_relIndex_sq_of_hyperplane (hW : ∀ w : W, w * w = 1) {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) {X : Subgroup (MulAut W)} (hXc : ∀ a ∈ X, ∀ b ∈ X, a * b = b * a)
    (hXp : ∀ a ∈ X, a ^ p = 1) {K : Subgroup W} (hKX : ∀ a ∈ X, ∀ k ∈ K, a k ∈ K)
    (hfix : fixV X ⊓ K = ⊥) {t : MulAut W} (ht : t * t = 1) (htK : ∀ k ∈ K, t k ∈ K)
    (htX : ∀ x ∈ X, t * x * t⁻¹ = x⁻¹) {D : Subgroup (MulAut W)} (hDX : D ≤ X)
    (hD : D.relIndex X = p) :
    Nat.card ↥(fixV D ⊓ K) ≤
      ((fixV (Subgroup.zpowers t) ⊓ (fixV D ⊓ K)).relIndex (fixV D ⊓ K)) ^ 2 := by
  have hXD : ¬ X ≤ D := by
    intro h
    have := Subgroup.relIndex_eq_one.2 h
    rw [hD] at this
    exact (Fact.out : p.Prime).one_lt.ne' this
  obtain ⟨x, hxX, hxD⟩ := Set.not_subset.1 hXD
  have ht1 : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  refine card_le_relIndex_sq_of_inverts_of_fix_eq_bot hW ?_ ?_ hp2 (hXp x hxX) ht (htX x hxX) ?_
  · intro c hc
    obtain ⟨hcD, hcK⟩ := Subgroup.mem_inf.1 hc
    refine Subgroup.mem_inf.2 ⟨fun d hd => ?_, hKX x hxX c hcK⟩
    have h1 := hXc d (hDX hd) x hxX
    have := congrArg (fun f : MulAut W => f c) h1
    simp only [MulAut.mul_apply] at this
    rw [this, hcD d hd]
  · intro c hc
    exact map_mem_fixV_inf_of_inverts ht htK htX hDX hc
  · rw [eq_bot_iff]
    intro v hv
    obtain ⟨hv1, hv2⟩ := Subgroup.mem_inf.1 hv
    obtain ⟨hv2D, hv2K⟩ := Subgroup.mem_inf.1 hv2
    have hvx := mem_fixV_zpowers_iff.1 hv1
    have hvX : v ∈ fixV (D ⊔ Subgroup.zpowers x) := mem_fixV_sup_zpowers hv2D hvx
    rw [sup_zpowers_eq_of_relIndex_eq_prime hDX hD hxX hxD] at hvX
    have : v ∈ fixV X ⊓ K := Subgroup.mem_inf.2 ⟨hvX, hv2K⟩
    rwa [hfix] at this

end HyperplaneFactor

section Main

variable {W : Type} [CommGroup W] [Finite W]

open scoped Classical in
theorem two_pow_le_index_sq_of_inverts_abelian (hW : ∀ w : W, w * w = 1) {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) {X T : Subgroup (MulAut W)} (hXc : ∀ a ∈ X, ∀ b ∈ X, a * b = b * a)
    (hXp : ∀ a ∈ X, a ^ p = 1) (hX : X ≠ ⊥)
    (hTX : T ≤ Subgroup.normalizer (X : Set (MulAut W))) {t : MulAut W} (ht : t * t = 1)
    (htX : ∀ x ∈ X, t * x * t⁻¹ = x⁻¹) {m : ℕ}
    (horb : ∀ D : Subgroup (MulAut W), D ≤ X → D.relIndex X = p →
      m ≤ (T ⊓ Subgroup.normalizer (D : Set (MulAut W))).relIndex T) :
    2 ^ (m * orderOf (2 : ZMod p)) ≤ (fixV (Subgroup.zpowers t)).index ^ 2 := by
  have hodd : Odd p := (Fact.out : Nat.Prime p).odd_of_ne_two hp2
  have hXodd : Odd (Nat.card X) := odd_card_of_pow_eq_one hodd hXp
  have hker := two_pow_le_card_ker_of_hyperplane_orbit hW hp2 hXc hXp hX hTX horb
  set K : Subgroup W := (normHom X).ker with hK
  have hKX : ∀ a ∈ X, ∀ k ∈ K, a k ∈ K := fun a ha k hk =>
    map_ker_normHom (Subgroup.le_normalizer ha) hk
  have hfix : fixV X ⊓ K = ⊥ := fixV_inf_ker_normHom hW hXodd
  have ht1 : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have htN : t ∈ Subgroup.normalizer (X : Set (MulAut W)) := by
    rw [Subgroup.mem_set_normalizer_iff]
    intro h
    refine ⟨fun hh => ?_, fun hh => ?_⟩
    · rw [htX h hh]
      exact X.inv_mem hh
    · have h2 := htX _ hh
      have h3 : t * (t * h * t⁻¹) * t⁻¹ = h := by
        rw [ht1]
        calc t * (t * h * t) * t = (t * t) * h * (t * t) := by group
          _ = h := by rw [ht, one_mul, mul_one]
      rw [h3] at h2
      rw [h2]
      exact X.inv_mem hh
  have htK : ∀ k ∈ K, t k ∈ K := fun k hk => map_ker_normHom htN hk
  have : Fintype (Subgroup (MulAut W)) := Fintype.ofFinite _
  let 𝒟 : Finset (Subgroup (MulAut W)) :=
    Finset.univ.filter (fun D => D ≤ X ∧ D.relIndex X = p)
  have h𝒟 : ∀ D, D ∈ 𝒟 ↔ D ≤ X ∧ D.relIndex X = p := fun D => by simp [𝒟]
  let e := hyperplaneEquiv hW hp2 hXc hXp hKX hfix 𝒟 h𝒟
  have he := hyperplaneEquiv_apply hW hp2 hXc hXp hKX hfix 𝒟 h𝒟
  have hsq : Nat.card ↥K ≤ ((fixV (Subgroup.zpowers t) ⊓ K).relIndex K) ^ 2 :=
    card_le_relIndex_sq_of_equiv (C := fun D : 𝒟 => fixV (D : Subgroup (MulAut W)) ⊓ K) e he
      (fun D c hc => map_mem_fixV_inf_of_inverts ht htK htX ((h𝒟 D).1 D.2).1 hc)
      (fun D => card_le_relIndex_sq_of_hyperplane hW hp2 hXc hXp hKX hfix ht htK htX
        ((h𝒟 D).1 D.2).1 ((h𝒟 D).1 D.2).2)
  have hidx : (fixV (Subgroup.zpowers t) ⊓ K).relIndex K ≤ (fixV (Subgroup.zpowers t)).index := by
    rw [Subgroup.inf_relIndex_right]
    exact Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
      (Subgroup.relIndex_dvd_index_of_normal _ _)
  calc 2 ^ (m * orderOf (2 : ZMod p)) ≤ Nat.card ↥K := hker
    _ ≤ ((fixV (Subgroup.zpowers t) ⊓ K).relIndex K) ^ 2 := hsq
    _ ≤ (fixV (Subgroup.zpowers t)).index ^ 2 := Nat.pow_le_pow_left hidx 2

end Main

end CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit
