module

public import CFSG.LocalAnalysis.QuasithinUnique.Defs
public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.C5Counting

public section

namespace CFSG.AGLEmbedding.L34Squeeze

open Subgroup
open scoped Pointwise

variable {G : Type*} [Group G]

theorem le_sup_of_sylow [Finite G] {p : ℕ} [hp : Fact p.Prime] {B C₀ R X : Subgroup G}
    (hBC : B ≤ normalizer (C₀ : Set G)) (hXC : X ≤ normalizer (C₀ : Set G))
    (hXN : X ≤ B ⊔ C₀) (hR : IsPGroup p R) (hX : IsPGroup p X) (hRX : R ≤ X) (hRB : R ≤ B)
    (hsyl : ¬ p ∣ R.relIndex B) : X ≤ R ⊔ C₀ := by
  have hRC : R ≤ normalizer (C₀ : Set G) := hRB.trans hBC
  have hJJ : R ⊔ C₀ ≤ X ⊔ C₀ := sup_le_sup_right hRX _
  have hJN : X ⊔ C₀ ≤ B ⊔ C₀ := sup_le hXN le_sup_right
  have h1 := CFSG.QuasithinUnique.C5.card_sup_mul_card_inf_of_le_normalizer hRC
  have h2 := CFSG.QuasithinUnique.C5.card_sup_mul_card_inf_of_le_normalizer hXC
  have h3 := CFSG.QuasithinUnique.C5.card_sup_mul_card_inf_of_le_normalizer hBC
  have ha := CFSG.QuasithinUnique.C5.card_eq_card_mul_relIndex hJJ
  have hb := CFSG.QuasithinUnique.C5.card_eq_card_mul_relIndex hJN
  have hc := CFSG.QuasithinUnique.C5.card_eq_card_mul_relIndex hRB
  have he := CFSG.QuasithinUnique.C5.card_eq_card_mul_relIndex
    (inf_le_inf_right C₀ hRB : R ⊓ C₀ ≤ B ⊓ C₀)
  obtain ⟨r, hr⟩ := hR.exists_card_eq
  obtain ⟨m, hm⟩ := hX.exists_card_eq
  obtain ⟨j, hj⟩ := (hR.to_le (inf_le_left : R ⊓ C₀ ≤ R)).exists_card_eq
  obtain ⟨i, hi⟩ := (hX.to_le (inf_le_left : X ⊓ C₀ ≤ X)).exists_card_eq
  set a := (R ⊔ C₀).relIndex (X ⊔ C₀) with hadef
  set b := (X ⊔ C₀).relIndex (B ⊔ C₀) with hbdef
  set c := R.relIndex B with hcdef
  set e := (R ⊓ C₀).relIndex (B ⊓ C₀) with hedef
  have hC0 : 0 < Nat.card C₀ := Nat.card_pos
  have hJ0 : 0 < Nat.card ↥(R ⊔ C₀) := Nat.card_pos
  have hp0 : 0 < p := hp.out.pos
  have key1 : a * p ^ (r + i) = p ^ (m + j) := by
    have e1 : Nat.card ↥(R ⊔ C₀) * p ^ j = p ^ r * Nat.card C₀ := by rw [← hj, ← hr]; exact h1
    have e2 : Nat.card ↥(R ⊔ C₀) * a * p ^ i = p ^ m * Nat.card C₀ := by
      rw [← hi, ← hm, ← ha]; exact h2
    have e3 : Nat.card C₀ * (a * p ^ (r + i)) * Nat.card ↥(R ⊔ C₀) =
        Nat.card C₀ * p ^ (m + j) * Nat.card ↥(R ⊔ C₀) := by
      calc Nat.card C₀ * (a * p ^ (r + i)) * Nat.card ↥(R ⊔ C₀)
          = (p ^ r * Nat.card C₀) * (Nat.card ↥(R ⊔ C₀) * a * p ^ i) := by ring
        _ = (Nat.card ↥(R ⊔ C₀) * p ^ j) * (p ^ m * Nat.card C₀) := by rw [e1, e2]
        _ = Nat.card C₀ * p ^ (m + j) * Nat.card ↥(R ⊔ C₀) := by ring
    have := Nat.eq_of_mul_eq_mul_right hJ0 e3
    exact Nat.eq_of_mul_eq_mul_left hC0 this
  have key2 : a * b * e = c := by
    have e1 : Nat.card ↥(R ⊔ C₀) * p ^ j = p ^ r * Nat.card C₀ := by rw [← hj, ← hr]; exact h1
    have e4 : Nat.card ↥(R ⊔ C₀) * a * b * (p ^ j * e) = p ^ r * c * Nat.card C₀ := by
      rw [← hj, ← he, ← hr, ← hc, ← ha, ← hb]; exact h3
    have e5 : (p ^ r * Nat.card C₀) * (a * b * e) = (p ^ r * Nat.card C₀) * c := by
      calc (p ^ r * Nat.card C₀) * (a * b * e)
          = (Nat.card ↥(R ⊔ C₀) * p ^ j) * (a * b * e) := by rw [e1]
        _ = Nat.card ↥(R ⊔ C₀) * a * b * (p ^ j * e) := by ring
        _ = p ^ r * c * Nat.card C₀ := e4
        _ = (p ^ r * Nat.card C₀) * c := by ring
    exact Nat.eq_of_mul_eq_mul_left (Nat.mul_pos (pow_pos hp0 r) hC0) e5
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow hp.out).mp (Dvd.intro _ key1)
  have ha1 : a = 1 := by
    rcases Nat.eq_zero_or_pos k with hk0 | hk0
    · rw [hk, hk0, pow_zero]
    · exfalso
      apply hsyl
      have hpa : p ∣ a := by
        rw [hk]; exact dvd_pow_self p (Nat.pos_iff_ne_zero.mp hk0)
      exact hpa.trans ⟨b * e, by rw [← key2]; ring⟩
  have hle : X ⊔ C₀ ≤ R ⊔ C₀ := Subgroup.relIndex_eq_one.mp ha1
  exact le_sup_left.trans hle
theorem exists_inv_mul_mem_normalizer [Finite G] {C₀ U : Subgroup G}
    (hU : CFSG.QuasithinUnique.IsSylowTwoOf U C₀) {n : G}
    (hn : n ∈ normalizer (C₀ : Set G)) :
    ∃ c ∈ C₀, c⁻¹ * n ∈ normalizer (U : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hUC, hU2, hidx⟩ := hU
  set φ : G →* G := (MulAut.conj n).toMonoidHom with hφdef
  have hφ : Function.Injective φ := (MulAut.conj n).injective
  have hC : C₀.map φ = C₀ := (Subgroup.mem_normalizer_iff_map_conj_eq).mp hn
  set U' := U.map φ with hU'def
  have hU'C : U' ≤ C₀ := hC ▸ Subgroup.map_mono hUC
  have hidx' : (U'.subgroupOf C₀).index = (U.subgroupOf C₀).index := by
    have := Subgroup.relIndex_map_map_of_injective U C₀ hφ
    rw [hC] at this
    exact this
  have hP1 : IsPGroup 2 (U.subgroupOf C₀) := hU2.comap_subtype
  have hP2 : IsPGroup 2 (U'.subgroupOf C₀) := (hU2.map φ).comap_subtype
  let P₁ : Sylow 2 C₀ := hP1.toSylow hidx
  let P₂ : Sylow 2 C₀ := hP2.toSylow (by rw [hidx']; exact hidx)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq C₀ P₁ P₂
  have hg' : (P₂ : Subgroup C₀) = (MulAut.conj g) • (P₁ : Subgroup C₀) := by
    rw [← hg, Sylow.coe_subgroup_smul]
  refine ⟨g, g.2, ?_⟩
  set x : G := (g : G)⁻¹ * n with hx
  have hsub : U.map (MulAut.conj x).toMonoidHom ≤ U := by
    rintro _ ⟨u, hu, rfl⟩
    have hnu : n * u * n⁻¹ ∈ U' := ⟨u, hu, by simp [hφdef, MulAut.conj_apply]⟩
    have hmem : (⟨n * u * n⁻¹, hU'C hnu⟩ : C₀) ∈ (P₂ : Subgroup C₀) :=
      Subgroup.mem_subgroupOf.mpr hnu
    rw [hg', Subgroup.pointwise_smul_def] at hmem
    obtain ⟨y, hy, hyeq⟩ := hmem
    have hyU : (y : G) ∈ U := Subgroup.mem_subgroupOf.mp hy
    have hyeq' : (g : G) * y * (g : G)⁻¹ = n * u * n⁻¹ := by
      have := congrArg Subtype.val hyeq
      simpa [MulAut.conj_apply] using this
    have : (MulAut.conj x).toMonoidHom u = y := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hx]
      rw [show (g : G)⁻¹ * n * u * ((g : G)⁻¹ * n)⁻¹ = (g : G)⁻¹ * (n * u * n⁻¹) * g by group,
        ← hyeq']
      group
    rw [this]
    exact hyU
  have hcard : Nat.card U ≤ Nat.card (U.map (MulAut.conj x).toMonoidHom) := by
    rw [Subgroup.card_map_of_injective (MulAut.conj x).injective]
  have heq := Subgroup.eq_of_le_of_card_ge hsub hcard
  exact (Subgroup.mem_normalizer_iff_map_conj_eq).mpr heq
def commImage (A : Subgroup G) (t : G) (hAab : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (htA : ∀ a ∈ A, t * a * t⁻¹ ∈ A) : Subgroup G where
  carrier := {d | ∃ a ∈ A, a * (t * a * t⁻¹)⁻¹ = d}
  one_mem' := ⟨1, A.one_mem, by group⟩
  mul_mem' := by
    rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    refine ⟨a * b, A.mul_mem ha hb, ?_⟩
    have hX : (t * a * t⁻¹)⁻¹ ∈ A := A.inv_mem (htA a ha)
    have hY : b * (t * b * t⁻¹)⁻¹ ∈ A := A.mul_mem hb (A.inv_mem (htA b hb))
    have hXY := hAab _ hX _ hY
    calc a * b * (t * (a * b) * t⁻¹)⁻¹
        = a * (b * (t * b * t⁻¹)⁻¹ * (t * a * t⁻¹)⁻¹) := by group
      _ = a * ((t * a * t⁻¹)⁻¹ * (b * (t * b * t⁻¹)⁻¹)) := by rw [hXY]
      _ = a * (t * a * t⁻¹)⁻¹ * (b * (t * b * t⁻¹)⁻¹) := by group
  inv_mem' := by
    rintro _ ⟨a, ha, rfl⟩
    refine ⟨a⁻¹, A.inv_mem ha, ?_⟩
    have h1 := hAab _ (A.inv_mem ha) _ (htA a ha)
    calc a⁻¹ * (t * a⁻¹ * t⁻¹)⁻¹ = a⁻¹ * (t * a * t⁻¹) := by group
      _ = t * a * t⁻¹ * a⁻¹ := h1
      _ = (a * (t * a * t⁻¹)⁻¹)⁻¹ := by group

theorem exists_ne_one_commute [Finite G] {U D : Subgroup G} (hU : IsPGroup 2 U)
    (hD : IsPGroup 2 D) (hUD : U ≤ normalizer (D : Set G)) (hD1 : D ≠ ⊥) :
    ∃ d ∈ D, d ≠ 1 ∧ ∀ u ∈ U, u * d = d * u := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P := U ⊔ D with hP
  have hPp : IsPGroup 2 P := hU.to_sup_of_normal_right' hD hUD
  have hDP : D ≤ P := le_sup_right
  have hPN : P ≤ normalizer (D : Set G) := sup_le hUD Subgroup.le_normalizer
  have : Group.IsNilpotent P := hPp.isNilpotent
  have hnormal : (D.subgroupOf P).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hPN
  have hne : D.subgroupOf P ≠ ⊥ := by
    intro h
    apply hD1
    rw [← Subgroup.map_subgroupOf_eq_of_le hDP, h, Subgroup.map_bot]
  obtain ⟨⟨y, hy⟩, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hne)
  refine ⟨(y : G), Subgroup.mem_subgroupOf.mp hy.1, fun h => hy1 ?_, fun u hu => ?_⟩
  · exact Subtype.ext (Subtype.ext h)
  · have := Subgroup.mem_center_iff.mp hy.2 ⟨u, (le_sup_left : U ≤ P) hu⟩
    exact congrArg Subtype.val this

theorem eq_one_of_pow_odd [Finite G] {A : Subgroup G} (hA : IsPGroup 2 A) {d : G} (hd : d ∈ A)
    {n : ℕ} (hn : Odd n) (hdn : d ^ n = 1) : d = 1 := by
  obtain ⟨k, hk⟩ := hA ⟨d, hd⟩
  have hk' : d ^ 2 ^ k = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  have h1 : orderOf d ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
  have h2 : orderOf d ∣ n := orderOf_dvd_of_pow_eq_one hdn
  have hcop : Nat.Coprime (2 ^ k) n := Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hn)
  have h3 : orderOf d ∣ 1 := by
    rw [← hcop.gcd_eq_one]; exact Nat.dvd_gcd h1 h2
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h3)

theorem pow_orderOf_eq_one_of_commute {a t : G} (hc : t * (a * (t * a * t⁻¹)⁻¹) =
    (a * (t * a * t⁻¹)⁻¹) * t) : (a * (t * a * t⁻¹)⁻¹) ^ orderOf t = 1 := by
  set d := a * (t * a * t⁻¹)⁻¹ with hd
  have hcomm : Commute t d := hc
  have hk : ∀ k : ℕ, d = t ^ k * a * (t ^ k)⁻¹ * (t ^ (k + 1) * a * (t ^ (k + 1))⁻¹)⁻¹ := by
    intro k
    have hck : t ^ k * d * (t ^ k)⁻¹ = d := by
      rw [(hcomm.pow_left k).eq]; group
    rw [← hck, hd, pow_succ]
    group
  have hpow : ∀ N : ℕ, d ^ N = a * (t ^ N * a * (t ^ N)⁻¹)⁻¹ := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      rw [pow_succ, ih, hk N]
      group
  rw [hpow, pow_orderOf_eq_one]
  group

theorem commute_of_commute_fixed [Finite G] {A U : Subgroup G} {t : G}
    (hAab : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hA2 : IsPGroup 2 A) (hU2 : IsPGroup 2 U)
    (htA : ∀ a ∈ A, t * a * t⁻¹ ∈ A) (hUA : ∀ u ∈ U, ∀ a ∈ A, u * a * u⁻¹ ∈ A)
    (hodd : Odd (orderOf t))
    (hcomm : ∀ u ∈ U, ∀ a ∈ A, (u * t * u⁻¹ * t⁻¹) * a = a * (u * t * u⁻¹ * t⁻¹))
    (hfix : ∀ a ∈ A, (∀ u ∈ U, u * a = a * u) → t * a = a * t) :
    ∀ a ∈ A, t * a = a * t := by
  set D := commImage A t hAab htA with hDdef
  have hDA : D ≤ A := by
    rintro _ ⟨a, ha, rfl⟩
    exact A.mul_mem ha (A.inv_mem (htA a ha))
  have hUD' : ∀ u ∈ U, ∀ d ∈ D, u * d * u⁻¹ ∈ D := by
    rintro u hu _ ⟨a, ha, rfl⟩
    have ha' : u * a * u⁻¹ ∈ A := hUA u hu a ha
    refine ⟨u * a * u⁻¹, ha', ?_⟩
    set c := u * t * u⁻¹ * t⁻¹ with hc
    have hca : c * (t * (u * a * u⁻¹) * t⁻¹) = (t * (u * a * u⁻¹) * t⁻¹) * c :=
      hcomm u hu _ (htA _ ha')
    have e1 : u * (t * a * t⁻¹) * u⁻¹ = c * (t * (u * a * u⁻¹) * t⁻¹) * c⁻¹ := by
      rw [hc]; group
    have e2 : c * (t * (u * a * u⁻¹) * t⁻¹) * c⁻¹ = t * (u * a * u⁻¹) * t⁻¹ := by
      rw [hca, mul_inv_cancel_right]
    calc u * a * u⁻¹ * (t * (u * a * u⁻¹) * t⁻¹)⁻¹
        = u * a * u⁻¹ * (u * (t * a * t⁻¹) * u⁻¹)⁻¹ := by rw [e1, e2]
      _ = u * (a * (t * a * t⁻¹)⁻¹) * u⁻¹ := by group
  have hUD : U ≤ normalizer (D : Set G) := by
    intro u hu
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · exact hUD' u hu h
    · intro h'
      have := hUD' u⁻¹ (U.inv_mem hu) _ h'
      simpa [mul_assoc] using this
  by_contra hne
  obtain ⟨a₀, ha₀, hnc⟩ : ∃ a ∈ A, ¬ t * a = a * t := by
    by_contra h
    exact hne fun a ha => by
      by_contra h'
      exact h ⟨a, ha, h'⟩
  have hD1 : D ≠ ⊥ := by
    intro hbot
    have hmem : a₀ * (t * a₀ * t⁻¹)⁻¹ ∈ D := ⟨a₀, ha₀, rfl⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    apply hnc
    have : a₀ = t * a₀ * t⁻¹ := mul_inv_eq_one.mp hmem
    calc t * a₀ = t * a₀ * t⁻¹ * t := by group
      _ = a₀ * t := by rw [← this]
  obtain ⟨d, hdD, hd1, hdU⟩ := exists_ne_one_commute hU2 (hA2.to_le hDA) hUD hD1
  have htd : t * d = d * t := hfix d (hDA hdD) hdU
  obtain ⟨a, ha, rfl⟩ := hdD
  exact hd1 (eq_one_of_pow_odd hA2 (hDA ⟨a, ha, rfl⟩) hodd (pow_orderOf_eq_one_of_commute htd))

end CFSG.AGLEmbedding.L34Squeeze
