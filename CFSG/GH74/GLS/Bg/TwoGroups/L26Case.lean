module

public import CFSG.GH74.GLS.Bg.TwoGroups.L26Cfg
public import CFSG.GH74.GLS.Bg.TwoGroups.Basic

public section

namespace CFSG.GH74.GLS.Bg.TwoGroups

namespace L26

@[expose] def SFacts (G : Type) [Group G] : Prop :=
  Nat.card G = 64 ∧ (∀ g : G, g ^ 4 = 1) ∧
  (∀ g h x : G, x * (g * h * g⁻¹ * h⁻¹) = (g * h * g⁻¹ * h⁻¹) * x) ∧
  (∀ g x : G, x * (g * g) = (g * g) * x) ∧
  (∀ z : G, (∀ x : G, x * z = z * x) → ∃ g h : G, g * h * g⁻¹ * h⁻¹ = z) ∧
  Nat.card {z : G // ∀ x : G, x * z = z * x} = 4

theorem SFacts.of_equiv {G G' : Type} [Group G] [Group G'] (e : G ≃* G') (h : SFacts G') :
    SFacts G := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨(Nat.card_congr e.toEquiv).trans h1, ?_, ?_, ?_, ?_, ?_⟩
  · intro g
    apply e.injective
    rw [map_pow, map_one]
    exact h2 (e g)
  · intro g h x
    apply e.injective
    simp only [map_mul, map_inv]
    exact h3 (e g) (e h) (e x)
  · intro g x
    apply e.injective
    simp only [map_mul]
    exact h4 (e g) (e x)
  · intro z hz
    have hz' : ∀ x' : G', x' * e z = e z * x' := by
      intro x'
      obtain ⟨x, rfl⟩ := e.surjective x'
      rw [← map_mul, ← map_mul, hz x]
    obtain ⟨g', h', hgh⟩ := h5 (e z) hz'
    refine ⟨e.symm g', e.symm h', ?_⟩
    apply e.injective
    simp only [map_mul, map_inv, MulEquiv.apply_symm_apply]
    exact hgh
  · refine (Nat.card_congr (e.toEquiv.subtypeEquiv (fun z => ?_))).trans h6
    constructor
    · intro hz x'
      obtain ⟨x, rfl⟩ := e.surjective x'
      show e x * e z = e z * e x
      rw [← map_mul, ← map_mul, hz x]
    · intro hz x
      apply e.injective
      simp only [map_mul]
      exact hz (e x)

@[expose] def K3Prop : Prop :=
  ∀ (T : Type) [Group T] [Finite T], IsPGroup 2 T → ∀ α : MulAut T, α ^ 3 = 1 →
    (∀ g : T, α g = g → g = 1) → ∀ A : Subgroup T, A.Normal → (∀ a ∈ A, α a ∈ A) →
    (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) →
    Nonempty (↥A ≃* Multiplicative (ZMod 8 × ZMod 8)) → Subgroup.centralizer (A : Set T) = A →
    Nat.card T = 4 * Nat.card A → ∀ g : T, ∀ h ∈ A, h ^ 4 = 1 → g * h * g⁻¹ = h

variable {T : Type} [Group T] [Finite T] {α t : MulAut T} {E : Subgroup T}

theorem Cfg.case_S (cfg : Cfg T α t E) [hEn : E.Normal] (A : Subgroup T) [hAn : A.Normal]
    (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hAα : ∀ a ∈ A, α a ∈ A) (hEA : E ≤ A)
    (hCA : Subgroup.centralizer (A : Set T) = A)
    (k : ℕ) (hk3 : 3 ≤ k) (a : T) (haA : a ∈ A) (hord : orderOf a = 2 ^ k)
    (hθ : Nonempty (↥A ≃* Multiplicative (ZMod (2 ^ k) × ZMod (2 ^ k))))
    (hSF : SFacts (T ⧸ E)) (hK3 : K3Prop) : False := by
  obtain ⟨hS64, hSexp, hScomm, hSsq, hSsurj, hScen⟩ := hSF
  have hmk : ∀ g : T, (QuotientGroup.mk g : T ⧸ E) ^ 4 = 1 := fun g => hSexp _
  have ha4E : a ^ 4 ∈ E := by
    have := hmk a
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at this
    exact this
  have ha8 : a ^ 8 = 1 := by
    have := cfg.E2 _ ha4E
    calc a ^ 8 = a ^ 4 * a ^ 4 := by rw [← pow_add]
      _ = 1 := this
  have hk : k = 3 := by
    have h1 : orderOf a ∣ 8 := orderOf_dvd_of_pow_eq_one ha8
    rw [hord] at h1
    have : 2 ^ k ∣ 2 ^ 3 := by simpa using h1
    have := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp this
    omega
  subst hk
  obtain ⟨θ⟩ := hθ
  have hθ' : Nonempty (↥A ≃* Multiplicative (ZMod 8 × ZMod 8)) := ⟨θ⟩
  have hAcard : Nat.card A = 64 := by
    rw [Nat.card_congr θ.toEquiv, Nat.card_eq_fintype_card]; decide
  have hTcard : Nat.card T = 4 * Nat.card A := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup E
    rw [cfg.Ecard, hS64] at h1
    omega
  have hK := hK3 T cfg.p2 α cfg.a3 cfg.hfix A hAn hAα hAc hθ' hCA hTcard
  let A2 : Subgroup T :=
    { carrier := {h | h ∈ A ∧ h ^ 4 = 1}
      mul_mem' := by
        rintro x y ⟨hx, hx4⟩ ⟨hy, hy4⟩
        refine ⟨mul_mem hx hy, ?_⟩
        rw [Commute.mul_pow (show Commute x y from hAc x hx y hy) 4, hx4, hy4, one_mul]
      one_mem' := ⟨one_mem A, one_pow 4⟩
      inv_mem' := by
        rintro x ⟨hx, hx4⟩
        exact ⟨inv_mem hx, by rw [inv_pow, hx4, inv_one]⟩ }
  have hA2mem : ∀ h, h ∈ A2 ↔ h ∈ A ∧ h ^ 4 = 1 := fun h => Iff.rfl
  have hA2card : Nat.card A2 = 16 := by
    have e1 : Nat.card A2 = Nat.card {x : ↥A // (x : T) ^ 4 = 1} :=
      Nat.card_congr
        { toFun := fun h => ⟨⟨h.1, h.2.1⟩, h.2.2⟩
          invFun := fun x => ⟨x.1.1, x.1.2, x.2⟩
          left_inv := fun h => rfl
          right_inv := fun x => rfl }
    have e2 : Nat.card {x : ↥A // (x : T) ^ 4 = 1} =
        Nat.card {y : Multiplicative (ZMod 8 × ZMod 8) // y ^ 4 = 1} :=
      Nat.card_congr (θ.toEquiv.subtypeEquiv (fun x => by
        show (x : T) ^ 4 = 1 ↔ θ x ^ 4 = 1
        rw [← map_pow, map_eq_one_iff θ θ.injective]
        exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩))
    rw [e1, e2, Nat.card_eq_fintype_card]
    decide +kernel
  let Z1 : Subgroup T := (Subgroup.center (T ⧸ E)).comap (QuotientGroup.mk' E)
  have hZ1mem : ∀ g : T, g ∈ Z1 ↔
      ∀ x : T ⧸ E, x * QuotientGroup.mk g = QuotientGroup.mk g * x := by
    intro g
    show (QuotientGroup.mk' E g) ∈ Subgroup.center (T ⧸ E) ↔ _
    rw [Subgroup.mem_center_iff]
    rfl
  have hcenterCard : Nat.card (Subgroup.center (T ⧸ E)) = 4 := by
    rw [← hScen]
    exact Nat.card_congr (Equiv.subtypeEquivRight (fun z => by rw [Subgroup.mem_center_iff]))
  have hZ1card : Nat.card Z1 = 16 := by
    have := card_comap_of_surjective (QuotientGroup.mk' E) (QuotientGroup.mk'_surjective E)
      (Subgroup.center (T ⧸ E))
    rw [QuotientGroup.ker_mk', hcenterCard, cfg.Ecard] at this
    exact this
  have hA2Z1 : A2 ≤ Z1 := by
    intro h hh
    rw [hZ1mem]
    intro x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    have := hK g h ((hA2mem h).mp hh).1 ((hA2mem h).mp hh).2
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    calc g * h = (g * h * g⁻¹) * g := by group
      _ = h * g := by rw [this]
  have hA2eq : A2 = Z1 := Subgroup.eq_of_le_of_card_ge hA2Z1 (by rw [hA2card, hZ1card])
  have hZ1A2 : ∀ g : T, g ∈ Z1 → g ∈ A2 := fun g hg => by rw [hA2eq]; exact hg
  have ha2 : a * a ∈ A2 := by
    refine ⟨mul_mem haA haA, ?_⟩
    calc (a * a) ^ 4 = a ^ 8 := by rw [← pow_two, ← pow_mul]
      _ = 1 := ha8
  have ha2Z : a * a ∈ Z1 := by rw [← hA2eq]; exact ha2
  have hcen : ∀ x : T ⧸ E, x * QuotientGroup.mk (a * a) = QuotientGroup.mk (a * a) * x :=
    (hZ1mem _).mp ha2Z
  obtain ⟨g', h', hgh⟩ := hSsurj (QuotientGroup.mk (a * a)) hcen
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective g'
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective h'
  obtain ⟨c, hc⟩ : ∃ c : T, c = x * y * x⁻¹ * y⁻¹ := ⟨_, rfl⟩
  have hcmk : (QuotientGroup.mk c : T ⧸ E) = QuotientGroup.mk (a * a) := by
    rw [hc]; simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]; exact hgh
  have hcZ : c ∈ Z1 := by
    rw [hZ1mem]
    intro z
    obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective z
    rw [hc]
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    exact hScomm _ _ _
  have hxxZ : x * x ∈ Z1 := by
    rw [hZ1mem]
    intro z
    obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective z
    simp only [QuotientGroup.mk_mul]
    exact hSsq _ _
  have hcA2 : c ∈ A2 := hZ1A2 c hcZ
  have hxxA2 : x * x ∈ A2 := hZ1A2 _ hxxZ
  have hcg : ∀ g : T, g * c = c * g := fun g => by
    calc g * c = (g * c * g⁻¹) * g := by group
      _ = c * g := by rw [hK g c hcA2.1 hcA2.2]
  have hxx : ∀ g : T, g * (x * x) = (x * x) * g := fun g => by
    calc g * (x * x) = (g * (x * x) * g⁻¹) * g := by group
      _ = (x * x) * g := by rw [hK g _ hxxA2.1 hxxA2.2]
  have hxy : x * y = c * y * x := by rw [hc]; group
  have hcc : c * c = 1 := by
    have E1 : x * x * y = c * c * (y * (x * x)) := by
      calc x * x * y = x * (x * y) := by group
        _ = x * (c * y * x) := by rw [hxy]
        _ = (x * c) * y * x := by group
        _ = (c * x) * y * x := by rw [hcg x]
        _ = c * (x * y) * x := by group
        _ = c * (c * y * x) * x := by rw [hxy]
        _ = c * c * (y * (x * x)) := by group
    rw [hxx y] at E1
    have : c * c * (x * x * y) = 1 * (x * x * y) := by rw [one_mul]; exact E1.symm
    exact mul_right_cancel this
  have he : c⁻¹ * (a * a) ∈ E := QuotientGroup.eq.mp hcmk
  obtain ⟨e, he_def⟩ : ∃ e : T, e = c⁻¹ * (a * a) := ⟨_, rfl⟩
  rw [← he_def] at he
  have hae : a * a = c * e := by rw [he_def]; group
  have hce : c * e = e * c := hAc c hcA2.1 e (hEA he)
  have h4 : a ^ 4 = 1 := by
    calc a ^ 4 = (a * a) * (a * a) := by simp [pow_succ, mul_assoc]
      _ = (c * e) * (c * e) := by rw [hae]
      _ = c * (e * c) * e := by group
      _ = c * (c * e) * e := by rw [← hce]
      _ = c * c * (e * e) := by group
      _ = 1 := by rw [hcc, cfg.E2 e he, one_mul]
  have h5 : orderOf a ∣ 4 := orderOf_dvd_of_pow_eq_one h4
  rw [hord] at h5
  norm_num at h5

theorem Cfg.abelian_case (cfg : Cfg T α t E) [hEn : E.Normal] (j : ℕ)
    (ε : (T ⧸ E) ≃* Multiplicative (ZMod (2 ^ j) × ZMod (2 ^ j))) :
    ∀ g h : T, g * h = h * g := by
  classical
  have hEc : ∀ e ∈ E, ∀ g : T, e * g = g * e := cfg.Ecen
  obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective
    (ε.symm (Multiplicative.ofAdd ((1 : ZMod (2 ^ j)), (0 : ZMod (2 ^ j)))))
  obtain ⟨y, hy⟩ := QuotientGroup.mk_surjective
    (ε.symm (Multiplicative.ofAdd ((0 : ZMod (2 ^ j)), (1 : ZMod (2 ^ j)))))
  have hεx : ε (QuotientGroup.mk x) =
      Multiplicative.ofAdd ((1 : ZMod (2 ^ j)), (0 : ZMod (2 ^ j))) := by
    rw [hx]; simp
  have hεy : ε (QuotientGroup.mk y) =
      Multiplicative.ofAdd ((0 : ZMod (2 ^ j)), (1 : ZMod (2 ^ j))) := by
    rw [hy]; simp
  have hcommT : ∀ a b : T ⧸ E, a * b = b * a := by
    intro a b
    apply ε.injective
    rw [map_mul, map_mul]
    exact mul_comm _ _
  obtain ⟨c, hc⟩ : ∃ c : T, c = x * y * x⁻¹ * y⁻¹ := ⟨_, rfl⟩
  have hcE : c ∈ E := by
    rw [← QuotientGroup.eq_one_iff, hc]
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    rw [hcommT (QuotientGroup.mk x) (QuotientGroup.mk y)]
    group
  have hcc : c * c = 1 := cfg.E2 c hcE
  have hgen : ∀ g : T, ∃ (i j' : ℕ) (e' : T), e' ∈ E ∧ g = x ^ i * y ^ j' * e' := by
    intro g
    obtain ⟨⟨p, q⟩, hpq⟩ : ∃ pq : ZMod (2 ^ j) × ZMod (2 ^ j),
        Multiplicative.ofAdd pq = ε (QuotientGroup.mk g) := ⟨(ε (QuotientGroup.mk g)).toAdd, rfl⟩
    refine ⟨p.val, q.val, (x ^ p.val * y ^ q.val)⁻¹ * g, ?_, by group⟩
    have h1 : (QuotientGroup.mk g : T ⧸ E) = QuotientGroup.mk (x ^ p.val * y ^ q.val) := by
      apply ε.injective
      rw [← hpq, QuotientGroup.mk_mul, map_mul, QuotientGroup.mk_pow, QuotientGroup.mk_pow,
        map_pow, map_pow, hεx, hεy, ← ofAdd_nsmul, ← ofAdd_nsmul, ← ofAdd_add]
      congr 1
      ext <;> simp
    rw [← QuotientGroup.eq]
    exact h1.symm
  have hSc : ∀ s ∈ Subgroup.zpowers c, ∀ g : T, s * g = g * s := by
    intro s hs g
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hs
    have h1 : c * g = g * c := hEc c hcE g
    exact ((Commute.zpow_left (show Commute c g from h1) n)).eq
  have hSn : (Subgroup.zpowers c).Normal := ⟨fun n hn g => by
    rw [← hSc n hn g, mul_assoc, mul_inv_cancel, mul_one]
    exact hn⟩
  have hSmem : ∀ s ∈ Subgroup.zpowers c, s = 1 ∨ s = c := by
    intro s hs
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hs
    obtain ⟨m, rfl | rfl⟩ := Int.even_or_odd' n
    · left; rw [zpow_mul, zpow_two, hcc, one_zpow]
    · right
      rw [zpow_add, zpow_mul, zpow_two, hcc, one_zpow, one_mul, zpow_one]
  have hcomm : ∀ g h : T, g * h * g⁻¹ * h⁻¹ ∈ Subgroup.zpowers c := by
    intro g h
    rw [← QuotientGroup.eq_one_iff]
    set X : T ⧸ Subgroup.zpowers c := QuotientGroup.mk x
    set Y : T ⧸ Subgroup.zpowers c := QuotientGroup.mk y
    have h0 : (QuotientGroup.mk c : T ⧸ Subgroup.zpowers c) = 1 :=
      (QuotientGroup.eq_one_iff c).mpr (Subgroup.mem_zpowers c)
    have h1 : (QuotientGroup.mk (x * y * x⁻¹ * y⁻¹) : T ⧸ Subgroup.zpowers c) = 1 := by
      rw [← hc]; exact h0
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv] at h1
    have hXY : Commute X Y := by
      show X * Y = Y * X
      calc X * Y = (X * Y * X⁻¹ * Y⁻¹) * (Y * X) := by group
        _ = Y * X := by rw [h1, one_mul]
    have hcenter : ∀ e' ∈ E, ∀ z : T ⧸ Subgroup.zpowers c,
        Commute (QuotientGroup.mk e' : T ⧸ Subgroup.zpowers c) z := by
      intro e' he' z
      obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective z
      show _ * _ = _ * _
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hEc e' he' w]
    have hform : ∀ g : T, ∃ (i j' : ℕ) (e' : T), e' ∈ E ∧
        (QuotientGroup.mk g : T ⧸ Subgroup.zpowers c) = X ^ i * Y ^ j' * QuotientGroup.mk e' := by
      intro g
      obtain ⟨i, j', e', he', rfl⟩ := hgen g
      exact ⟨i, j', e', he', by simp [X, Y, QuotientGroup.mk_mul, QuotientGroup.mk_pow]⟩
    have hcm : ∀ a b : T, (QuotientGroup.mk a : T ⧸ Subgroup.zpowers c) * QuotientGroup.mk b =
        QuotientGroup.mk b * QuotientGroup.mk a := by
      intro a b
      obtain ⟨i, j', e1, he1, ha⟩ := hform a
      obtain ⟨k, l, e2, he2, hb⟩ := hform b
      rw [ha, hb]
      have c1 : Commute (X ^ i) (X ^ k) := (Commute.refl X).pow_pow i k
      have c2 : Commute (X ^ i) (Y ^ l) := hXY.pow_pow i l
      have c3 : Commute (Y ^ j') (X ^ k) := (hXY.symm).pow_pow j' k
      have c4 : Commute (Y ^ j') (Y ^ l) := (Commute.refl Y).pow_pow j' l
      have hA : Commute (X ^ i * Y ^ j') (X ^ k * Y ^ l) :=
        Commute.mul_left (Commute.mul_right c1 c2) (Commute.mul_right c3 c4)
      exact (Commute.mul_left (Commute.mul_right hA (hcenter e2 he2 _).symm)
        (Commute.mul_right (hcenter e1 he1 _) (hcenter e1 he1 _))).eq
    have := hcm g h
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    rw [this]
    group
  have hc1 : c = 1 := by
    by_contra hc1
    have h1 := hcomm (α x) (α y)
    have h2 : α c = α x * α y * (α x)⁻¹ * (α y)⁻¹ := by rw [hc]; simp
    rw [← h2] at h1
    rcases hSmem _ h1 with h | h
    · exact hc1 ((map_eq_one_iff α α.injective).mp h)
    · exact hc1 (cfg.Efpf c hcE h)
  intro g h
  have h1 := hcomm g h
  rcases hSmem _ h1 with h2 | h2
  · exact (commutatorElement_eq_one_iff_mul_comm.mp (by simpa [commutatorElement_def] using h2))
  · rw [hc1] at h2
    exact (commutatorElement_eq_one_iff_mul_comm.mp (by simpa [commutatorElement_def] using h2))

end L26

end CFSG.GH74.GLS.Bg.TwoGroups
