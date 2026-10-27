module

public import CFSG.LargeExtraspecial.AS35MQuotSet

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module CFSG.RankThree.OrthogonalInvolutions CQuotE

namespace AS35M

variable {G : Type} [Group G]

theorem commute_inv_iff {x y : G} : y * x⁻¹ = x⁻¹ * y ↔ y * x = x * y := by
  constructor
  · intro h
    calc y * x = x * (x⁻¹ * y) * x := by group
      _ = x * (y * x⁻¹) * x := by rw [h]
      _ = x * y := by group
  · intro h
    calc y * x⁻¹ = x⁻¹ * (x * y) * x⁻¹ := by group
      _ = x⁻¹ * (y * x) * x⁻¹ := by rw [h]
      _ = x⁻¹ * y := by group

theorem conj_inv_cases {x c : G} (hcx : c * x * c⁻¹ = x ∨ c * x * c⁻¹ = x⁻¹) :
    c⁻¹ * x * c⁻¹⁻¹ = x ∨ c⁻¹ * x * c⁻¹⁻¹ = x⁻¹ := by
  rcases hcx with h | h
  · left
    calc c⁻¹ * x * c⁻¹⁻¹ = c⁻¹ * (c * x * c⁻¹) * c⁻¹⁻¹ := by rw [h]
      _ = x := by group
  · right
    calc c⁻¹ * x * c⁻¹⁻¹ = (c⁻¹ * x⁻¹ * c)⁻¹ := by group
      _ = (c⁻¹ * (c * x * c⁻¹) * c)⁻¹ := by rw [h]
      _ = x⁻¹ := by group

theorem commute_conj_iff {x c : G} (hcx : c * x * c⁻¹ = x ∨ c * x * c⁻¹ = x⁻¹) (y : G) :
    y * x = x * y ↔ c * y * c⁻¹ * x = x * (c * y * c⁻¹) := by
  have key : y * x = x * y ↔ c * y * c⁻¹ * (c * x * c⁻¹) = c * x * c⁻¹ * (c * y * c⁻¹) := by
    constructor
    · intro h
      calc c * y * c⁻¹ * (c * x * c⁻¹) = c * (y * x) * c⁻¹ := by group
        _ = c * (x * y) * c⁻¹ := by rw [h]
        _ = c * x * c⁻¹ * (c * y * c⁻¹) := by group
    · intro h
      calc y * x = c⁻¹ * (c * y * c⁻¹ * (c * x * c⁻¹)) * c := by group
        _ = c⁻¹ * (c * x * c⁻¹ * (c * y * c⁻¹)) * c := by rw [h]
        _ = x * y := by group
  rw [key]
  rcases hcx with h | h
  · rw [h]
  · rw [h]
    exact commute_inv_iff

theorem isPGroup_zpowers_of_pow_prime {H : Type} [Group H] {p : ℕ} (hp : p.Prime) {g : H}
    (hg : g ^ p = 1) : IsPGroup p (zpowers g) := by
  rcases (Nat.dvd_prime hp).mp (orderOf_dvd_of_pow_eq_one hg) with h | h
  · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h, pow_zero])
  · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h, pow_one])

theorem eq_one_or_eq_of_mem_zpowers_of_orderOf_two {z y : G} (hz : orderOf z = 2)
    (hy : y ∈ zpowers z) : y = 1 ∨ y = z := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hy
  rw [← zpow_mod_orderOf, hz]
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · left
    rw [show ((2 : ℕ) : ℤ) = 2 from rfl, h, zpow_zero]
  · right
    rw [show ((2 : ℕ) : ℤ) = 2 from rfl, h, zpow_one]

end AS35M

open AS35M

namespace Setting

variable {G : Type} [Group G] (S : Setting G)

@[expose] def KCx (x : G) : Subgroup G :=
  S.M ⊓ centralizer ({x} : Set G) ⊓
    centralizer ((S.QG ⊓ centralizer ({x} : Set G) : Subgroup G) : Set G)

theorem mem_KCx {x c : G} : c ∈ S.KCx x ↔
    c ∈ S.M ∧ c * x = x * c ∧ ∀ q ∈ S.QG ⊓ centralizer ({x} : Set G), c * q = q * c := by
  change (c ∈ S.M ∧ c ∈ centralizer ({x} : Set G)) ∧
    c ∈ centralizer ((S.QG ⊓ centralizer ({x} : Set G) : Subgroup G) : Set G) ↔ _
  rw [mem_centralizer_singleton_iff (g := x), mem_centralizer_iff]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨h1, h2, fun q hq => (h3 q hq).symm⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨⟨h1, h2⟩, fun q hq => (h3 q hq).symm⟩

@[expose] def EOdd (x : G) : Subgroup G :=
  closure {c | c ∈ S.KCx x ∧ Odd (orderOf c)}

theorem EOdd_le_KCx (x : G) : S.EOdd x ≤ S.KCx x := by
  rw [EOdd, closure_le]
  exact fun c hc => hc.1

theorem mem_EOdd_of_odd {x c : G} (hc : c ∈ S.KCx x) (hco : Odd (orderOf c)) :
    c ∈ S.EOdd x :=
  subset_closure ⟨hc, hco⟩

theorem z_mem_KCx {x : G} (hxM : x ∈ S.M) : S.z ∈ S.KCx x :=
  (S.mem_KCx).mpr ⟨S.zM.2, (S.z_comm hxM).symm, fun _ hq => (S.z_comm_QG (mem_inf.mp hq).1).symm⟩

theorem self_mem_KCx {x : G} (hxM : x ∈ S.M) : x ∈ S.KCx x :=
  (S.mem_KCx).mpr ⟨hxM, rfl, fun _ hq => (mem_centralizer_singleton_iff.mp
    (mem_inf.mp hq).2).symm⟩

theorem self_mem_EOdd {x : G} (hxM : x ∈ S.M) (hxo : Odd (orderOf x)) : x ∈ S.EOdd x :=
  S.mem_EOdd_of_odd (S.self_mem_KCx hxM) hxo

theorem conj_mem_KCx {x c : G} (hcM : c ∈ S.M)
    (hcx : c * x * c⁻¹ = x ∨ c * x * c⁻¹ = x⁻¹) {k : G} (hk : k ∈ S.KCx x) :
    c * k * c⁻¹ ∈ S.KCx x := by
  obtain ⟨hkM, hkx, hkq⟩ := (S.mem_KCx).mp hk
  refine (S.mem_KCx).mpr ⟨S.M.mul_mem (S.M.mul_mem hcM hkM) (S.M.inv_mem hcM),
    (commute_conj_iff hcx k).mp hkx, ?_⟩
  intro q hq
  obtain ⟨hqQ, hqx⟩ := mem_inf.mp hq
  have hqx' := mem_centralizer_singleton_iff.mp hqx
  have hcx' := conj_inv_cases hcx
  have h1 : c⁻¹ * q * c ∈ S.QG ⊓ centralizer ({x} : Set G) := by
    refine mem_inf.mpr ⟨?_, mem_centralizer_singleton_iff.mpr ?_⟩
    · have := S.conj_mem_QG (S.M.inv_mem hcM) hqQ
      rwa [inv_inv] at this
    · have := (commute_conj_iff hcx' q).mp hqx'
      rwa [inv_inv] at this
  have h3 := hkq _ h1
  calc c * k * c⁻¹ * q = c * (k * (c⁻¹ * q * c)) * c⁻¹ := by group
    _ = c * ((c⁻¹ * q * c) * k) * c⁻¹ := by rw [h3]
    _ = q * (c * k * c⁻¹) := by group

theorem conj_mem_EOdd {x c : G} (hcM : c ∈ S.M)
    (hcx : c * x * c⁻¹ = x ∨ c * x * c⁻¹ = x⁻¹) {e : G} (he : e ∈ S.EOdd x) :
    c * e * c⁻¹ ∈ S.EOdd x := by
  have hle : S.EOdd x ≤ (S.EOdd x).comap (MulAut.conj c).toMonoidHom := by
    rw [EOdd, closure_le]
    rintro k ⟨hk, hko⟩
    rw [SetLike.mem_coe, mem_comap]
    refine subset_closure ⟨S.conj_mem_KCx hcM hcx hk, ?_⟩
    change Odd (orderOf (MulAut.conj c k))
    rwa [MulEquiv.orderOf_eq]
  exact hle he

theorem conj_inv_mem_EOdd {x c : G} (hcM : c ∈ S.M)
    (hcx : c * x * c⁻¹ = x ∨ c * x * c⁻¹ = x⁻¹) {e : G} (he : e ∈ S.EOdd x) :
    c⁻¹ * e * c ∈ S.EOdd x := by
  have := S.conj_mem_EOdd (S.M.inv_mem hcM) (conj_inv_cases hcx) he
  rwa [inv_inv] at this

theorem KCx_inv (x : G) : S.KCx x⁻¹ = S.KCx x := by
  ext c
  rw [S.mem_KCx, S.mem_KCx]
  have hset : S.QG ⊓ centralizer ({x⁻¹} : Set G) = S.QG ⊓ centralizer ({x} : Set G) := by
    ext q
    simp only [mem_inf, mem_centralizer_singleton_iff]
    exact and_congr_right fun _ => commute_inv_iff
  rw [hset, commute_inv_iff]

theorem EOdd_inv (x : G) : S.EOdd x⁻¹ = S.EOdd x := by
  rw [EOdd, EOdd, KCx_inv]

theorem descentSet_EOdd {x : G} (hxM : x ∈ S.M) (hxo : Odd (orderOf x)) :
    S.DescentSet (S.EOdd x : Set G) x where
  le_M _ he := ((S.mem_KCx).mp (S.EOdd_le_KCx x he)).1
  mem := S.self_mem_EOdd hxM hxo
  comm _ he := ((S.mem_KCx).mp (S.EOdd_le_KCx x he)).2.1
  cent _ he := ((S.mem_KCx).mp (S.EOdd_le_KCx x he)).2.2

variable [Finite G]

theorem exists_commute_rho_eq_of_pow_three {x : G} (hxM : x ∈ S.M) (hx3 : x ^ 3 = 1)
    {m : G} (hmM : m ∈ S.M)
    (hm : S.ρ ⟨m, hmM⟩ * S.ρ ⟨x, hxM⟩ = S.ρ ⟨x, hxM⟩ * S.ρ ⟨m, hmM⟩) :
    ∃ c : G, ∃ hc : c ∈ S.M, c * x = x * c ∧ S.ρ ⟨c, hc⟩ = S.ρ ⟨m, hmM⟩ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set xM : S.M := ⟨x, hxM⟩ with hxMdef
  set mM : S.M := ⟨m, hmM⟩ with hmMdef
  set H : Subgroup S.M := (zpowers (S.ρ xM)).comap S.ρ with hH
  have hxH : xM ∈ H := mem_comap.mpr (mem_zpowers _)
  have hyH : mM * xM * mM⁻¹ ∈ H := by
    rw [hH, mem_comap, map_mul, map_mul, map_inv, hm, mul_assoc, mul_inv_cancel, mul_one]
    exact mem_zpowers _
  set x₁ : H := ⟨xM, hxH⟩
  set y₁ : H := ⟨mM * xM * mM⁻¹, hyH⟩
  have hx₁ : x₁ ^ 3 = 1 := Subtype.ext (Subtype.ext (by simpa using hx3))
  have hy₁ : y₁ ^ 3 = 1 := Subtype.ext (Subtype.ext (by
    change ((mM * xM * mM⁻¹) ^ 3 : S.M).1 = 1
    rw [conj_pow]
    simp [xM, mM, hx3]))
  obtain ⟨P₁, hP₁⟩ := (isPGroup_zpowers_of_pow_prime Nat.prime_three hx₁).exists_le_sylow
  obtain ⟨P₂, hP₂⟩ := (isPGroup_zpowers_of_pow_prime Nat.prime_three hy₁).exists_le_sylow
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq H P₂ P₁
  have hx₁P : x₁ ∈ (P₁ : Subgroup H) := hP₁ (mem_zpowers _)
  have hy₁P : h * y₁ * h⁻¹ ∈ (P₁ : Subgroup H) := by
    rw [← hh, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    convert hP₂ (mem_zpowers y₁) using 1
    simp
    group
  set ρH : H →* S.O := S.ρ.comp H.subtype with hρH
  have hinj : ∀ a ∈ (P₁ : Subgroup H), ρH a = 1 → a = 1 := by
    intro a ha h1
    obtain ⟨k, hk⟩ := P₁.isPGroup' ⟨a, ha⟩
    have hk' : a ^ 3 ^ k = 1 := congrArg Subtype.val hk
    have haQ : ((a : S.M) : G) ∈ S.QG := (S.ρ_eq_one_iff _).mp h1
    have h4 : a ^ 4 = 1 := Subtype.ext (Subtype.ext (by
      simpa using S.pow_four_of_mem_QG haQ))
    have h5 : orderOf a ∣ Nat.gcd (3 ^ k) 4 :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hk') (orderOf_dvd_of_pow_eq_one h4)
    have h6 : Nat.gcd (3 ^ k) 4 = 1 :=
      Nat.Coprime.pow_left k (by norm_num : Nat.Coprime 3 4)
    rw [h6, Nat.dvd_one, orderOf_eq_one_iff] at h5
    exact h5
  have hρh : ρH h ∈ zpowers (S.ρ xM) := h.2
  obtain ⟨i, hi⟩ := mem_zpowers_iff.mp hρh
  have hc1 : ρH (h * y₁ * h⁻¹) = ρH x₁ := by
    rw [map_mul, map_mul, map_inv, ← hi]
    change S.ρ xM ^ i * S.ρ (mM * xM * mM⁻¹) * (S.ρ xM ^ i)⁻¹ = S.ρ xM
    rw [map_mul, map_mul, map_inv, hm, mul_assoc (S.ρ xM), mul_inv_cancel, mul_one,
      (Commute.zpow_left (Commute.refl (S.ρ xM)) i).eq, mul_inv_cancel_right]
  have hc2 : h * y₁ * h⁻¹ = x₁ := by
    have h7 := hinj ((h * y₁ * h⁻¹) * x₁⁻¹) (mul_mem hy₁P (inv_mem hx₁P))
      (by rw [map_mul, map_inv, hc1, mul_inv_cancel])
    rw [mul_inv_eq_one] at h7
    exact h7
  have hc3 : ((h : S.M) : G) * m * x * m⁻¹ * ((h : S.M) : G)⁻¹ = x := by
    have := congrArg (fun w : H => ((w : S.M) : G)) hc2
    simpa [y₁, x₁, xM, mM, mul_assoc] using this
  refine ⟨x ^ (-i) * ((h : S.M) : G) * m,
    S.M.mul_mem (S.M.mul_mem (S.M.zpow_mem hxM _) (h : S.M).2) hmM, ?_, ?_⟩
  · calc x ^ (-i) * ((h : S.M) : G) * m * x
        = x ^ (-i) * (((h : S.M) : G) * m * x * m⁻¹ * ((h : S.M) : G)⁻¹) *
            (((h : S.M) : G) * m) := by group
      _ = x ^ (-i) * x * (((h : S.M) : G) * m) := by rw [hc3]
      _ = x * (x ^ (-i) * ((h : S.M) : G) * m) := by group
  · have e : (⟨x ^ (-i) * ((h : S.M) : G) * m,
        S.M.mul_mem (S.M.mul_mem (S.M.zpow_mem hxM _) (h : S.M).2) hmM⟩ : S.M) =
        xM ^ (-i) * (h : S.M) * mM := rfl
    rw [e, map_mul, map_mul, map_zpow]
    change S.ρ xM ^ (-i) * ρH h * S.ρ mM = S.ρ mM
    rw [← hi, ← zpow_add, neg_add_cancel, zpow_zero, one_mul]

@[expose] def MbarOddHyp {x : G} (hxM : x ∈ S.M) : Prop :=
  ∀ σ ∈ S.Mbar, σ * S.ρ ⟨x, hxM⟩ = S.ρ ⟨x, hxM⟩ * σ →
    (∀ v ∈ fixSpace (S.rhoL hxM), (σ : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v) → Odd (orderOf σ)

@[expose] def MbarOTwoHyp {x : G} (hxM : x ∈ S.M) : Prop :=
  ∀ R : Subgroup S.O, R ≤ S.Mbar → (∀ σ ∈ R, σ * S.ρ ⟨x, hxM⟩ = S.ρ ⟨x, hxM⟩ * σ) →
    (∀ τ ∈ S.Mbar, τ * S.ρ ⟨x, hxM⟩ = S.ρ ⟨x, hxM⟩ * τ → ∀ σ ∈ R, τ * σ * τ⁻¹ ∈ R) →
      IsPGroup 2 R → R = ⊥

theorem odd_or_odd_mul_z {x : G} (hxM : x ∈ S.M) (hx3 : x ^ 3 = 1) (hN1 : S.MbarOddHyp hxM)
    {c : G} (hc : c ∈ S.KCx x) : Odd (orderOf c) ∨ Odd (orderOf (c * S.z)) := by
  obtain ⟨hcM, hcx, hcq⟩ := (S.mem_KCx).mp hc
  set σ := S.ρ ⟨c, hcM⟩ with hσ
  have hσx : σ * S.ρ ⟨x, hxM⟩ = S.ρ ⟨x, hxM⟩ * σ := by
    rw [hσ, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hcx
  have hσfix : ∀ v ∈ fixSpace (S.rhoL hxM), (σ : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v := by
    intro v hv
    rw [← S.cqxSub_eq_fixSpace_of_pow_three hxM hx3] at hv
    obtain ⟨q, hq, hqQ, rfl⟩ := S.mem_clSub_iff.mp hv
    change S.rhoL hcM (S.cl q) = S.cl q
    rw [S.rhoL_cl hcM hqQ, hcq q hq]
    congr 1
    group
  have hm := hN1 σ ⟨⟨c, hcM⟩, rfl⟩ hσx hσfix
  set m := orderOf σ with hmdef
  have hcmQ : c ^ m ∈ S.QG := by
    have h1 : S.ρ ⟨c ^ m, S.M.pow_mem hcM m⟩ = 1 := by
      change S.ρ (⟨c, hcM⟩ ^ m) = 1
      rw [map_pow, ← hσ, pow_orderOf_eq_one]
    exact (S.ρ_eq_one_iff _).mp h1
  have hcmK : c ^ m ∈ S.KCx x := pow_mem hc m
  have hcmz : c ^ m ∈ zpowers S.z := by
    obtain ⟨-, hcmx, hcmq⟩ := (S.mem_KCx).mp hcmK
    exact S.mem_zpowers_of_commute_cqx hxM hx3
      (mem_inf.mpr ⟨hcmQ, mem_centralizer_singleton_iff.mpr hcmx⟩) hcmq
  rcases eq_one_or_eq_of_mem_zpowers_of_orderOf_two S.orderOf_z hcmz with h | h
  · left
    exact Odd.of_dvd_nat hm (orderOf_dvd_of_pow_eq_one h)
  · right
    refine Odd.of_dvd_nat hm (orderOf_dvd_of_pow_eq_one ?_)
    have hcz : Commute c S.z := S.z_comm hcM
    obtain ⟨j, hj⟩ := hm
    rw [hcz.mul_pow, h, hj, pow_succ, pow_mul, pow_two, S.z_mul_z, one_pow, one_mul, S.z_mul_z]

theorem quotCentHypE_EOdd {x : G} (hxM : x ∈ S.M) (hx3 : orderOf x = 3)
    (hN1 : S.MbarOddHyp hxM) : S.QuotCentHypE (S.EOdd x : Set G) := by
  have hxo : Odd (orderOf x) := by rw [hx3]; decide
  have hE := S.descentSet_EOdd hxM hxo
  intro c hcM hcE hcq
  have hcK : c ∈ S.KCx x := (S.mem_KCx).mpr ⟨hcM, (mem_centralizer_iff.mp hcE x hE.mem).symm,
    fun q hq => by
      rw [← hE.QG_inf] at hq
      exact hcq q (mem_inf.mp hq).1 (mem_inf.mp hq).2⟩
  have key : ∀ e : G, e ∈ S.EOdd x → e ∈ centralizer (S.EOdd x : Set G) →
      Odd (orderOf e) → IsOddCentralE (S.EOdd x : Set G) e⁻¹ := by
    intro e he heE heo
    refine ⟨inv_mem heE, fun y hy => ?_, by rwa [orderOf_inv]⟩
    have h1 := mem_centralizer_iff.mp hy e he
    calc e⁻¹ * y = e⁻¹ * (y * e) * e⁻¹ := by group
      _ = e⁻¹ * (e * y) * e⁻¹ := by rw [h1]
      _ = y * e⁻¹ := by group
  rcases S.odd_or_odd_mul_z hxM (pow_three_of_orderOf hx3) hN1 hcK with h | h
  · exact ⟨c⁻¹, key c (S.mem_EOdd_of_odd hcK h) hcE h, by rw [mul_inv_cancel]; exact one_mem _⟩
  · have hczK : c * S.z ∈ S.KCx x := mul_mem hcK (S.z_mem_KCx hxM)
    refine ⟨(c * S.z)⁻¹, key _ (S.mem_EOdd_of_odd hczK h) (mul_mem hcE hE.z_mem) h, ?_⟩
    have hcz : c * S.z = S.z * c := S.z_comm hcM
    rw [show c * (c * S.z)⁻¹ = S.z⁻¹ by rw [hcz]; group, S.z_inv]
    exact S.z_mem_QG

end Setting

end CFSG.LargeExtraspecial
