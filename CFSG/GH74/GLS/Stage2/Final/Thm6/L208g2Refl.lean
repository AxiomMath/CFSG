module

public import CFSG.GH74.GLS.IVK.L2.Involutions
public import CFSG.GH74.GLS.Stage2.Final.Thm6.L208g2Bar

public section

namespace CFSG.GH74.GLS.Stage2.Final.Thm6.L208g2

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Stage2.Final
  CFSG.GorensteinWalter

section Dihedral

theorem zmod_two_torsion_unique {m : ℕ} [NeZero m] {i j : ZMod m} (hi : i + i = 0) (hj : j + j = 0)
    (hi0 : i ≠ 0) (hj0 : j ≠ 0) : i = j := by
  have key : ∀ x : ZMod m, x + x = 0 → x ≠ 0 → 2 * x.val = m := by
    intro x hx hx0
    have h1 : ((2 * x.val : ℕ) : ZMod m) = 0 := by
      rw [Nat.cast_mul, Nat.cast_ofNat, ZMod.natCast_zmod_val]
      linear_combination hx
    have h2 : m ∣ 2 * x.val := (ZMod.natCast_eq_zero_iff _ _).1 h1
    obtain ⟨c, hc⟩ := h2
    have hlt : x.val < m := ZMod.val_lt x
    have hpos : 0 < x.val := Nat.pos_of_ne_zero (fun h => hx0 ((ZMod.val_eq_zero x).1 h))
    have hm : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
    have hc1 : c < 2 := by
      by_contra hcc
      push Not at hcc
      have : m * 2 ≤ m * c := Nat.mul_le_mul_left m hcc
      omega
    have hc2 : c ≠ 0 := by
      rintro rfl
      omega
    have : c = 1 := by omega
    subst this
    omega
  apply ZMod.val_injective m
  have := key i hi hi0
  have := key j hj hj0
  omega

theorem dihedral_reflection {m : ℕ} (hm : 3 ≤ m) {c e : DihedralGroup m} (hc2 : c * c = 1) (hc1 : c ≠ 1)
    (hcc : ∀ x : DihedralGroup m, x * c = c * x) (he2 : e * e = 1) (he1 : e ≠ 1) (hec : e ≠ c)
    {k : DihedralGroup m} (hk : Odd (orderOf k)) : e * k * e⁻¹ = k⁻¹ := by
  have : NeZero m := ⟨by omega⟩
  obtain ⟨j, rfl⟩ : ∃ j : ZMod m, c = DihedralGroup.r j := by
    cases c with
    | r j => exact ⟨j, rfl⟩
    | sr j =>
      exfalso
      have h1 := hcc (DihedralGroup.r 1)
      simp only [DihedralGroup.r_mul_sr, DihedralGroup.sr_mul_r] at h1
      have h2 : j - 1 = j + 1 := by
        have := DihedralGroup.sr.inj h1
        exact this
      have h3 : (2 : ZMod m) = 0 := by linear_combination (-1 : ZMod m) * h2
      have h4 : m ∣ 2 := (ZMod.natCast_eq_zero_iff 2 m).1 (by exact_mod_cast h3)
      have := Nat.le_of_dvd (by norm_num) h4
      omega
  have hj2 : j + j = 0 := by
    have := hc2
    simp only [DihedralGroup.r_mul_r] at this
    exact DihedralGroup.r.inj (by simpa using this)
  have hj0 : j ≠ 0 := fun h => hc1 (by rw [h]; rfl)
  cases e with
  | r i =>
    exfalso
    have hi2 : i + i = 0 := by
      have := he2
      simp only [DihedralGroup.r_mul_r] at this
      exact DihedralGroup.r.inj (by simpa using this)
    have hi0 : i ≠ 0 := fun h => he1 (by rw [h]; rfl)
    exact hec (by rw [zmod_two_torsion_unique hi2 hj2 hi0 hj0])
  | sr i =>
    cases k with
    | r l =>
      simp only [DihedralGroup.inv_sr, DihedralGroup.sr_mul_r, DihedralGroup.inv_r,
        DihedralGroup.sr_mul_sr]
      congr 1
      ring
    | sr l =>
      exfalso
      rw [DihedralGroup.orderOf_sr] at hk
      exact absurd hk (by decide)

end Dihedral

section PGL

variable {X : Type} [Group X] {F : Type} [Field F] [Finite F]

theorem isOddPrimePower_of_odd (h : Odd (Nat.card F)) : IsOddPrimePower (Nat.card F) := by
  let : Fintype F := Fintype.ofFinite F
  obtain ⟨p, _, n, hp, hcard⟩ := FiniteField.card' F
  have hpodd : Odd p := h.of_dvd_nat (by
    rw [Nat.card_eq_fintype_card, hcard]
    exact dvd_pow_self p (by have := n.pos; omega))
  exact ⟨p, n, hp, hpodd, by have := n.pos; omega, by
    simpa only [Nat.card_eq_fintype_card] using hcard⟩

theorem pgl2_reflection (ψ : X ≃* PGL2 F) (hodd : Odd (Nat.card F)) (hq : 3 < Nat.card F)
    {u ε : X} (hu2 : u * u = 1) (hu1 : u ≠ 1) (he2 : ε * ε = 1) (he1 : ε ≠ 1) (hne : ε ≠ u)
    (hcomm : ε * u = u * ε) {k : X} (hku : k * u = u * k) (hk : Odd (orderOf k)) :
    ε * k * ε⁻¹ = k⁻¹ := by
  have hF := isOddPrimePower_of_odd hodd
  obtain ⟨ε₀, hε₁, hε⟩ : ∃ ε₀ : ℤ, (ε₀ = 1 ∨ ε₀ = -1) ∧ (Nat.card F : ℤ) ≡ ε₀ [ZMOD 4] := by
    obtain ⟨t, ht⟩ := hodd
    rcases Nat.even_or_odd t with ⟨s, hs⟩ | ⟨s, hs⟩
    · exact ⟨1, Or.inl rfl, by unfold Int.ModEq; omega⟩
    · exact ⟨-1, Or.inr rfl, by unfold Int.ModEq; omega⟩
  have hordu : orderOf u = 2 := orderOf_eq_prime (by rwa [← sq] at hu2) hu1
  have hA2 : orderOf (ψ u) = 2 := by rw [MulEquiv.orderOf_eq]; exact hordu
  have hdih := IVK.pgl2_involution_centralizer_dihedral hF hq hε₁ hε hA2
  obtain ⟨m, hm3, ⟨θ₀⟩⟩ : ∃ m : ℕ, 3 ≤ m ∧
      Nonempty (↥(centralizer ({ψ u} : Set (PGL2 F))) ≃* DihedralGroup m) := by
    by_cases hin : ψ u ∈ (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range
    · obtain ⟨m, hm, hθ⟩ := hdih.1 hin
      exact ⟨m, by rcases hε₁ with rfl | rfl <;> omega, hθ⟩
    · obtain ⟨m, hm, hθ⟩ := hdih.2 hin
      exact ⟨m, by rcases hε₁ with rfl | rfl <;> omega, hθ⟩
  have hmapc : (centralizer ({u} : Set X)).map ψ.toMonoidHom = centralizer ({ψ u} : Set (PGL2 F)) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hy' : y ∈ centralizer ({u} : Set X) := hy
      rw [Subgroup.mem_centralizer_iff] at hy'
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      rw [hh]
      have := hy' u rfl
      simp only [MulEquiv.coe_toMonoidHom]
      rw [← map_mul, ← map_mul, this]
    · intro hx
      refine ⟨ψ.symm x, ?_, by simp⟩
      show ψ.symm x ∈ centralizer ({u} : Set X)
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      rw [hh]
      have := Subgroup.mem_centralizer_iff.mp hx (ψ u) rfl
      apply ψ.injective
      simp only [map_mul, MulEquiv.apply_symm_apply]
      exact this
  let φ : ↥(centralizer ({u} : Set X)) ≃* ↥(centralizer ({ψ u} : Set (PGL2 F))) :=
    (MulEquiv.subgroupMap ψ (centralizer ({u} : Set X))).trans (MulEquiv.subgroupCongr hmapc)
  let θ : ↥(centralizer ({u} : Set X)) ≃* DihedralGroup m := φ.trans θ₀
  have hu' : u ∈ centralizer ({u} : Set X) := Subgroup.mem_centralizer_iff.mpr fun h hh => by
    rw [Set.mem_singleton_iff] at hh; rw [hh]
  have he' : ε ∈ centralizer ({u} : Set X) := Subgroup.mem_centralizer_iff.mpr fun h hh => by
    rw [Set.mem_singleton_iff] at hh; rw [hh]; exact hcomm.symm
  have hk' : k ∈ centralizer ({u} : Set X) := Subgroup.mem_centralizer_iff.mpr fun h hh => by
    rw [Set.mem_singleton_iff] at hh; rw [hh]; exact hku.symm
  have hres := dihedral_reflection (m := m) hm3 (c := θ ⟨u, hu'⟩) (e := θ ⟨ε, he'⟩)
    (k := θ ⟨k, hk'⟩)
    (by rw [← map_mul]; exact (by rw [show (⟨u, hu'⟩ : ↥(centralizer ({u} : Set X))) * ⟨u, hu'⟩ = 1 from
        Subtype.ext hu2, map_one]))
    (fun h => hu1 (by
      have := θ.injective (h.trans (map_one θ).symm)
      exact congrArg Subtype.val this))
    (fun x => by
      obtain ⟨y, rfl⟩ := θ.surjective x
      rw [← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      exact (Subgroup.mem_centralizer_iff.mp y.2 u rfl).symm)
    (by rw [← map_mul]; exact (by rw [show (⟨ε, he'⟩ : ↥(centralizer ({u} : Set X))) * ⟨ε, he'⟩ = 1 from
        Subtype.ext he2, map_one]))
    (fun h => he1 (by
      have := θ.injective (h.trans (map_one θ).symm)
      exact congrArg Subtype.val this))
    (fun h => hne (by
      have := θ.injective h
      exact congrArg Subtype.val this))
    (by rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk]; exact hk)
  have h3 : θ ((⟨ε, he'⟩ : ↥(centralizer ({u} : Set X))) * ⟨k, hk'⟩ * ⟨ε, he'⟩⁻¹) =
      θ ((⟨k, hk'⟩ : ↥(centralizer ({u} : Set X)))⁻¹) := by
    rw [map_mul, map_mul, map_inv, map_inv]
    exact hres
  exact congrArg Subtype.val (θ.injective h3)

end PGL

section Reflect

variable {Y : Type} [Group Y] [Finite Y] {Sb Rb Lk Lk' : Subgroup Y} {r r' : ℕ}

theorem Factor.reflect (h : Factor Sb Rb Lk Lk' r r') {a e : Y} (ha : a ∈ Lk) (ha2 : a * a ≠ 1)
    (hsq : ∀ c ∈ Lk, c * (a * a) = (a * a) * c) (he2 : e * e = 1)
    (hea : e * a * e⁻¹ * a⁻¹ ∈ Lk ⊓ Lk')
    (hE1 : ¬ ∀ x ∈ Lk, e * x = x * e) (hE2 : ¬ ∀ x ∈ Lk, (e * a) * x = x * (e * a)) :
    ∀ k ∈ Lk, Odd (orderOf k) → k * a = a * k → e * k * e⁻¹ = k⁻¹ := by
  intro k hk hko hka
  have hnorm := h.normal
  obtain ⟨hnT, F₀, iF, fF, hcardF, ⟨ψ₀⟩⟩ := h.ind
  have hr := h.gt
  have hrodd := h.odd
  have he2' : e⁻¹ = e := inv_eq_of_mul_eq_one_right he2
  obtain ⟨x, hx⟩ := exists_conj_mem_sylow h.syl (y := e) ⟨1, by simpa [sq] using he2⟩
  set T : Subgroup Y := Lk ⊔ Sb with hT
  set N' : Subgroup ↥T := (centralizer (Lk : Set Y)).subgroupOf T with hN'
  have hconjLk : ∀ y ∈ Lk, ∀ g : Y, g⁻¹ * y * g ∈ Lk := fun y hy g => by
    simpa using hnorm.conj_mem y hy g⁻¹
  have hTLk : ∀ y ∈ Lk, y ∈ T := fun y hy => Subgroup.mem_sup_left hy
  have hTSb : ∀ y ∈ Sb, y ∈ T := fun y hy => Subgroup.mem_sup_right hy
  have hcls : ∀ (y : Y) (hy : y ∈ T),
      (QuotientGroup.mk (⟨y, hy⟩ : ↥T) : ↥T ⧸ N') = 1 ↔ ∀ c ∈ Lk, c * y = y * c := by
    intro y hy
    rw [QuotientGroup.eq_one_iff, hN', Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff]
    exact Iff.rfl
  have hmul : ∀ (y y' : Y) (hy : y ∈ T) (hy' : y' ∈ T),
      (QuotientGroup.mk (⟨y, hy⟩ : ↥T) : ↥T ⧸ N') * QuotientGroup.mk ⟨y', hy'⟩ =
        QuotientGroup.mk ⟨y * y', mul_mem hy hy'⟩ := fun _ _ _ _ => rfl
  have hinv : ∀ (y : Y) (hy : y ∈ T),
      (QuotientGroup.mk (⟨y, hy⟩ : ↥T) : ↥T ⧸ N')⁻¹ = QuotientGroup.mk ⟨y⁻¹, inv_mem hy⟩ :=
    fun _ _ => rfl
  have hconj_cen : ∀ y : Y, (∀ c ∈ Lk, c * (x⁻¹ * y * x) = (x⁻¹ * y * x) * c) ↔
      ∀ c ∈ Lk, c * y = y * c := by
    intro y
    constructor
    · intro hyc c hc
      have hc₀ := hconjLk c hc x
      have := hyc _ hc₀
      calc c * y = x * ((x⁻¹ * c * x) * (x⁻¹ * y * x)) * x⁻¹ := by group
        _ = x * ((x⁻¹ * y * x) * (x⁻¹ * c * x)) * x⁻¹ := by rw [this]
        _ = y * c := by group
    · intro hy c hc
      have hc₁ : x * c * x⁻¹ ∈ Lk := by simpa using hconjLk c hc x⁻¹
      calc c * (x⁻¹ * y * x) = x⁻¹ * ((x * c * x⁻¹) * y) * x := by group
        _ = x⁻¹ * (y * (x * c * x⁻¹)) * x := by rw [hy _ hc₁]
        _ = (x⁻¹ * y * x) * c := by group
  have hak : x⁻¹ * a * x ∈ Lk := hconjLk a ha x
  have hkk : x⁻¹ * k * x ∈ Lk := hconjLk k hk x
  have hee : x⁻¹ * e * x ∈ Sb := hx
  set ε : ↥T ⧸ N' := QuotientGroup.mk ⟨x⁻¹ * e * x, hTSb _ hee⟩ with hε
  set u : ↥T ⧸ N' := QuotientGroup.mk ⟨x⁻¹ * a * x, hTLk _ hak⟩ with hu
  set κ : ↥T ⧸ N' := QuotientGroup.mk ⟨x⁻¹ * k * x, hTLk _ hkk⟩ with hκ
  have hε2 : ε * ε = 1 := by
    rw [hε, hmul, hcls]
    intro c hc
    have : x⁻¹ * e * x * (x⁻¹ * e * x) = 1 := by
      calc x⁻¹ * e * x * (x⁻¹ * e * x) = x⁻¹ * (e * e) * x := by group
        _ = 1 := by rw [he2]; group
    rw [this]; simp
  have hu2 : u * u = 1 := by
    rw [hu, hmul, hcls]
    have := (hconj_cen (a * a)).2 (fun c hc => hsq c hc)
    intro c hc
    have h2 := this c hc
    have e2 : x⁻¹ * (a * a) * x = x⁻¹ * a * x * (x⁻¹ * a * x) := by group
    rw [e2] at h2
    exact h2
  have hε1 : ε ≠ 1 := by
    intro h1
    apply hE1
    rw [hε, hcls] at h1
    intro c hc
    exact ((hconj_cen e).1 h1 c hc).symm
  have hu1 : u ≠ 1 := by
    intro h1
    rw [hu, hcls] at h1
    exact h.toPair.not_cen_of_sq ha ha2 ((hconj_cen a).1 h1)
  have hεu : ε ≠ u := by
    intro h1
    apply hE2
    rw [hε, hu, QuotientGroup.eq, hN', Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff] at h1
    have h2 : ∀ c ∈ Lk, c * (e⁻¹ * a) = (e⁻¹ * a) * c := by
      apply (hconj_cen (e⁻¹ * a)).1
      intro c hc
      have := h1 c hc
      simp only [Subgroup.coe_mul, Subgroup.coe_inv] at this
      have e2 : x⁻¹ * (e⁻¹ * a) * x = (x⁻¹ * e * x)⁻¹ * (x⁻¹ * a * x) := by group
      rw [e2]
      exact this
    rw [he2'] at h2
    intro c hc
    exact (h2 c hc).symm
  have hεu_comm : ε * u = u * ε := by
    have h1 : ε * u * ε⁻¹ * u⁻¹ = 1 := by
      rw [hε, hu, hinv, hinv, hmul, hmul, hmul, hcls]
      intro c hc
      have e2 : x⁻¹ * (e * a * e⁻¹ * a⁻¹) * x =
          x⁻¹ * e * x * (x⁻¹ * a * x) * (x⁻¹ * e * x)⁻¹ * (x⁻¹ * a * x)⁻¹ := by group
      rw [← e2]
      exact (hconj_cen (e * a * e⁻¹ * a⁻¹)).2
        (fun c hc => (h.toPair.comm' _ hea.2 c hc).symm) c hc
    have h2 := mul_inv_eq_one.1 h1
    exact mul_inv_eq_iff_eq_mul.1 h2
  have hκu : κ * u = u * κ := by
    rw [hκ, hu, hmul, hmul]
    congr 1
    apply Subtype.ext
    show x⁻¹ * k * x * (x⁻¹ * a * x) = x⁻¹ * a * x * (x⁻¹ * k * x)
    calc x⁻¹ * k * x * (x⁻¹ * a * x) = x⁻¹ * (k * a) * x := by group
      _ = x⁻¹ * (a * k) * x := by rw [hka]
      _ = x⁻¹ * a * x * (x⁻¹ * k * x) := by group
  have hpowk : (x⁻¹ * k * x) ^ (orderOf k) = 1 := by
    have := conj_pow (a := x⁻¹) (b := k) (i := orderOf k)
    simp only [inv_inv] at this
    rw [this, pow_orderOf_eq_one]
    group
  have hκo : Odd (orderOf κ) := by
    have h1 : κ ^ (orderOf k) = 1 := by
      rw [hκ, ← QuotientGroup.mk_pow]
      have : (⟨x⁻¹ * k * x, hTLk _ hkk⟩ : ↥T) ^ (orderOf k) = 1 := Subtype.ext hpowk
      rw [this]
      rfl
    exact Odd.of_dvd_nat hko (orderOf_dvd_of_pow_eq_one h1)
  have hεκ : ε * κ * ε⁻¹ = κ⁻¹ :=
    pgl2_reflection ψ₀ (by rw [hcardF]; exact hrodd) (by rw [hcardF]; exact hr) hu2 hu1 hε2 hε1 hεu
      hεu_comm hκu hκo
  have hw1 : ε * κ * ε⁻¹ * κ = 1 := by rw [hεκ]; exact inv_mul_cancel κ
  rw [hε, hκ, hinv, hmul, hmul, hmul, hcls] at hw1
  have hw2 : ∀ c ∈ Lk, c * (e * k * e⁻¹ * k) = (e * k * e⁻¹ * k) * c := by
    apply (hconj_cen (e * k * e⁻¹ * k)).1
    intro c hc
    have e2 : x⁻¹ * e * x * (x⁻¹ * k * x) * (x⁻¹ * e * x)⁻¹ * (x⁻¹ * k * x) =
        x⁻¹ * (e * k * e⁻¹ * k) * x := by group
    rw [← e2]
    exact hw1 c hc
  have hk' : e * k * e⁻¹ ∈ Lk := by simpa using hnorm.conj_mem k hk e
  have hwL : e * k * e⁻¹ * k ∈ Lk := mul_mem hk' hk
  have hwL' : e * k * e⁻¹ * k ∈ Lk' := h.toPair.cen hwL hw2
  have hww : (e * k * e⁻¹ * k) * (e * k * e⁻¹ * k) = 1 := h.toPair.sq_of_mem_inf ⟨hwL, hwL'⟩
  have hkk'c : k * (e * k * e⁻¹) = (e * k * e⁻¹) * k := by
    have h1 := hw2 k hk
    have h2 : k * (e * k * e⁻¹) * k = (e * k * e⁻¹) * k * k := by
      calc k * (e * k * e⁻¹) * k = k * (e * k * e⁻¹ * k) := by group
        _ = (e * k * e⁻¹ * k) * k := h1
        _ = (e * k * e⁻¹) * k * k := by group
    exact mul_right_cancel h2
  have hpow2 : (e * k * e⁻¹ * k) ^ (orderOf k) = 1 := by
    have hc : Commute (e * k * e⁻¹) k := hkk'c.symm
    rw [hc.mul_pow]
    have := conj_pow (a := e) (b := k) (i := orderOf k)
    rw [this, pow_orderOf_eq_one]
    group
  have hw1' : e * k * e⁻¹ * k = 1 := by
    have h1 : orderOf (e * k * e⁻¹ * k) ∣ 2 := by
      apply orderOf_dvd_of_pow_eq_one
      rw [pow_two]
      exact hww
    have h2 : orderOf (e * k * e⁻¹ * k) ∣ orderOf k := orderOf_dvd_of_pow_eq_one hpow2
    have h3 : orderOf (e * k * e⁻¹ * k) ∣ Nat.gcd 2 (orderOf k) := Nat.dvd_gcd h1 h2
    have h4 : Nat.gcd 2 (orderOf k) = 1 := by
      have : Nat.Coprime 2 (orderOf k) := (Nat.coprime_two_left).2 hko
      exact this
    rw [h4] at h3
    exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 h3)
  exact eq_inv_of_mul_eq_one_left hw1'

end Reflect

end CFSG.GH74.GLS.Stage2.Final.Thm6.L208g2
