module

public import CFSG.GH74.GLS.Stage4.RestX2Q1
public import CFSG.GH74.GLS.Stage4.T6Rle
public import CFSG.GroupTheory.QuasisimpleCommutingProductBound

public section

namespace CFSG.GH74.GLS.Stage4.Rest.T6

open Subgroup CFSG.GH74.GLS.Stage4.Hex CFSG.GH74.GLS.Stage4.Rest.T2
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G] {N : T2N3 G} {u : G} {p : ℕ}

theorem M₂_le_normalizer_R₂ (N : T2N3 G) (p : ℕ) : M₂ N ≤ Subgroup.normalizer (R₂ N p : Set G) :=
  fun _ hm => Subgroup.mem_normalizer_fintype (fun _ hr => R₂_norm N p hm hr)

theorem card_RXP (h : T6Ctx N u p) {P₀ : Subgroup G} (hP₀F : P₀ ≤ N.F) (hP₀p : IsPGroup p ↥P₀) :
    IsPGroup p ↥((R₂ N p ⊔ N.X₁) ⊔ P₀) ∧
      Nat.card ↥((R₂ N p ⊔ N.X₁) ⊔ P₀) = Nat.card ↥(R₂ N p) * N.q₁ * Nat.card ↥P₀ := by
  have hloc := h.sec5.loc
  have hF5 := h.sec5.F5
  have hX₁K : N.X₁ ≤ N.K₁ := by rw [hloc.K₁_eq]; exact le_sup_left
  have hX₂K : N.X₂ ≤ N.K₂ := by rw [hloc.K₂_eq]; exact le_sup_left
  have hXn : N.X₁ ≤ Subgroup.normalizer (R₂ N p : Set G) := fun g hg =>
    M₂_le_normalizer_R₂ N p (K₁_le_M₂ h (hX₁K hg))
  have hRX : Disjoint (R₂ N p) N.X₁ := by
    rw [disjoint_iff, eq_bot_iff]
    intro x hx
    have : x ∈ R₂ N p ⊓ N.K₁ := ⟨hx.1, hX₁K hx.2⟩
    rwa [R₂_inf_K₁ h] at this
  have hcard₁ : Nat.card ↥(R₂ N p ⊔ N.X₁) = Nat.card ↥(R₂ N p) * N.q₁ := by
    rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _ hXn hRX, hloc.card_X₁]
  have hP₀R : P₀ ≤ Subgroup.normalizer (R₂ N p : Set G) := fun g hg =>
    M₂_le_normalizer_R₂ N p (F_le_M₂ h (hP₀F hg))
  have hmul : (↑(R₂ N p ⊔ N.X₁) : Set G) = (R₂ N p : Set G) * (N.X₁ : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left (R₂ N p) N.X₁ hXn
  have hP₀n : P₀ ≤ Subgroup.normalizer ((R₂ N p ⊔ N.X₁ : Subgroup G) : Set G) := by
    intro f hf
    refine Subgroup.mem_normalizer_fintype (fun t ht => ?_)
    have ht' : t ∈ (R₂ N p : Set G) * (N.X₁ : Set G) := by rw [← hmul]; exact ht
    obtain ⟨r, hr, x, hx, rfl⟩ := ht'
    have e : f * (r * x) * f⁻¹ = (f * r * f⁻¹) * (f * x * f⁻¹) := by group
    rw [e]
    refine Subgroup.mul_mem_sup ?_ ?_
    · exact R₂_norm N p (F_le_M₂ h (hP₀F hf)) hr
    · exact hF5.F_normX₁ f (hP₀F hf) x hx
  have hdisj : Disjoint (R₂ N p ⊔ N.X₁) P₀ := by
    rw [disjoint_iff, eq_bot_iff]
    intro g hg
    obtain ⟨hgS, hgP⟩ := hg
    have hg' : g ∈ (R₂ N p : Set G) * (N.X₁ : Set G) := by rw [← hmul]; exact hgS
    obtain ⟨r, hr, x, hx, rfl⟩ := hg'
    have hgF : r * x ∈ N.F := hP₀F hgP
    have hgz : (r * x) * N.z = N.z * (r * x) := h.FS _ hgF N.z hloc.z_mem_S
    have hxz : x * N.z = N.z * x := h.zK x (Subgroup.mem_sup_left (hX₁K hx))
    have hrz' : r * N.z = N.z * r := by
      have h1 : r * N.z * x = N.z * r * x := by
        calc r * N.z * x = r * (N.z * x) := by group
          _ = r * (x * N.z) := by rw [hxz]
          _ = (r * x) * N.z := by group
          _ = N.z * (r * x) := hgz
          _ = N.z * r * x := by group
      exact mul_right_cancel h1
    have hrz : N.z * r * N.z⁻¹ = r := by
      calc N.z * r * N.z⁻¹ = (r * N.z) * N.z⁻¹ := by rw [hrz']
        _ = r := by group
    have hrX₂ : r ∈ N.X₂ := R₂_Cz h r hr hrz
    have hrK : r ∈ N.K₁ ⊔ N.K₂ := Subgroup.mem_sup_right (hX₂K hrX₂)
    have hxK : x ∈ N.K₁ ⊔ N.K₂ := Subgroup.mem_sup_left (hX₁K hx)
    have hbot : r * x ∈ N.F ⊓ (N.K₁ ⊔ N.K₂) := ⟨hgF, Subgroup.mul_mem _ hrK hxK⟩
    rw [hF5.F_inter_K] at hbot
    exact hbot
  have hcard₂ : Nat.card ↥((R₂ N p ⊔ N.X₁) ⊔ P₀) = Nat.card ↥(R₂ N p ⊔ N.X₁) * Nat.card ↥P₀ :=
    CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _ hP₀n hdisj
  refine ⟨?_, by rw [hcard₂, hcard₁]⟩
  have : Fact p.Prime := ⟨h.prime⟩
  obtain ⟨a, ha⟩ := (R₂_pGroup N h.prime).exists_card_eq
  obtain ⟨c, hc⟩ := hP₀p.exists_card_eq
  obtain ⟨m, hm⟩ := h.q₁_pow
  exact IsPGroup.of_card (n := a + m + c) (by rw [hcard₂, hcard₁, ha, hm, hc]; ring)


theorem R_le_W' (h : T6Ctx N u p) {R : Subgroup G} (hRp : IsPGroup p ↥R) (hRC : R ≤ C₂ N)
    (hRinv : ∀ r ∈ R, N.z * r * N.z⁻¹ * r ∈ N.X₂) : R ≤ Wsub N := by
  intro r hr
  have hrC₂ : r ∈ C₂ N := hRC hr
  obtain ⟨c', hc'C, k, hk, hrck, hc'z⟩ := Zstar_C₂ h r hrC₂
  have hzM := z_mem_M₂ h
  have hc'M : c' ∈ M₂ N := C₂_le_M₂ hc'C
  have hk₂ : N.z * k * N.z⁻¹ ∈ Wsub N := Wsub_norm hzM hk
  have hk₃ : c' * (N.z * k * N.z⁻¹) * c'⁻¹ ∈ Wsub N := Wsub_norm hc'M hk₂
  have hx : N.z * r * N.z⁻¹ * r ∈ Wsub N := X₂_le_W h (hRinv r hr)
  have hzc' : N.z * c' * N.z⁻¹ = c' := by
    calc N.z * c' * N.z⁻¹ = (c' * N.z) * N.z⁻¹ := by rw [hc'z]
      _ = c' := by group
  have hzr : N.z * r * N.z⁻¹ = c' * (N.z * k * N.z⁻¹) := by
    rw [hrck]
    calc N.z * (c' * k) * N.z⁻¹ = (N.z * c' * N.z⁻¹) * (N.z * k * N.z⁻¹) := by group
      _ = c' * (N.z * k * N.z⁻¹) := by rw [hzc']
  have hcc : c' * c' ∈ Wsub N := by
    have e : c' * c' = (c' * (N.z * k * N.z⁻¹) * c'⁻¹)⁻¹ * (N.z * r * N.z⁻¹ * r) * k⁻¹ := by
      rw [hzr, hrck]; group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hk₃) hx) (Subgroup.inv_mem _ hk)
  have hk₄ : c'⁻¹ * k * c' ∈ Wsub N := by
    have := Wsub_norm ((M₂ N).inv_mem hc'M) hk
    simpa using this
  have hrr : r * r ∈ Wsub N := by
    have e : r * r = (c' * c') * (c'⁻¹ * k * c') * k := by rw [hrck]; group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hcc hk₄) hk
  exact mem_of_sq_mem (t6_odd_of_pGroup h.prime h.p_ne_two hRp hr) hrr

theorem R_le_R₂' (h : T6Ctx N u p) {R : Subgroup G} (hRp : IsPGroup p ↥R) (hRC : R ≤ C₂ N)
    (hRinv : ∀ r ∈ R, N.z * r * N.z⁻¹ * r ∈ N.X₂) : R ≤ R₂ N p := by
  have : Fact p.Prime := ⟨h.prime⟩
  have hnil := W_nilp h
  have hRW : R ≤ Wsub N := R_le_W' h hRp hRC hRinv
  have hRp' : IsPGroup p ↥(R.subgroupOf (Wsub N)) :=
    hRp.of_equiv (Subgroup.subgroupOfEquivOfLe hRW).symm
  obtain ⟨S, hRS⟩ := hRp'.exists_le_sylow
  have hSn : (S : Subgroup ↥(Wsub N)).Normal := Group.IsNilpotent.sylow_normal hnil p S
  have hSc : (S : Subgroup ↥(Wsub N)).Characteristic := Sylow.characteristic_of_normal S hSn
  set P : Subgroup G := (S : Subgroup ↥(Wsub N)).map (Wsub N).subtype with hP
  have hPnorm : Subgroup.normalizer (Wsub N : Set G) ≤ Subgroup.normalizer (P : Set G) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic _
  have hMW : M₂ N ≤ Subgroup.normalizer (Wsub N : Set G) := fun m hm =>
    Subgroup.mem_normalizer_fintype (fun w hw => Wsub_norm hm hw)
  have hPW : P ≤ Wsub N := Subgroup.map_subtype_le _
  have hPM : P ≤ M₂ N := hPW.trans (Wsub_le_C₂.trans C₂_le_M₂)
  have hPp : IsPGroup p ↥P := S.isPGroup'.map _
  have hle := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer p hPM (hMW.trans hPnorm) hPp
  intro r hr
  exact hle ⟨⟨r, hRW hr⟩, hRS (Subgroup.mem_subgroupOf.2 hr), rfl⟩


structure PairData (N : T2N3 G) (p : ℕ) (v : G) (B₁ B₂ : Subgroup G) : Prop where
  p₁ : IsPGroup p ↥B₁
  p₂ : IsPGroup p ↥B₂
  C₁ : B₁ ≤ C₂ N
  C₂ : B₂ ≤ C₂ N
  z₁ : ∀ r ∈ B₁, N.z * r * N.z⁻¹ * r ∈ N.X₂
  z₂ : ∀ r ∈ B₂, N.z * r * N.z⁻¹ * r ∈ N.X₂
  v₁ : B₁ ≤ Subgroup.centralizer {v}
  v₂ : B₂ ≤ Subgroup.centralizer {v}
  comm : ∀ x ∈ B₁, ∀ y ∈ B₂, x * y = y * x
  inf : B₁ ⊓ B₂ = ⊥

theorem PairData.card_le (h : T6Ctx N u p) {v : G} {B₁ B₂ : Subgroup G} (hd : PairData N p v B₁ B₂) :
    Nat.card ↥B₁ * Nat.card ↥B₂ ≤ Nat.card ↥(R₂ N p ⊓ Subgroup.centralizer {v}) := by
  have hR₁ := R_le_R₂' h hd.p₁ hd.C₁ hd.z₁
  have hR₂ := R_le_R₂' h hd.p₂ hd.C₂ hd.z₂
  have hle : B₁ ⊔ B₂ ≤ R₂ N p ⊓ Subgroup.centralizer {v} :=
    sup_le (le_inf hR₁ hd.v₁) (le_inf hR₂ hd.v₂)
  have hcard := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute B₁ B₂ hd.comm).1
  rw [hd.inf, Subgroup.card_bot, mul_one] at hcard
  calc Nat.card ↥B₁ * Nat.card ↥B₂ = Nat.card ↥(B₁ ⊔ B₂) := hcard.symm
    _ ≤ _ := Subgroup.card_le_of_le hle

theorem card_R₂_ge (h : T6Ctx N u p) {B₁ B₂ B₃ B₄ : Subgroup G} (hd : PairData N p u B₁ B₂)
    (hd' : PairData N p (N.z * u) B₃ B₄) :
    N.q₂ * ((Nat.card ↥B₁ * Nat.card ↥B₂) * (Nat.card ↥B₃ * Nat.card ↥B₄)) ≤ Nat.card ↥(R₂ N p) := by
  rw [R₂_card_eq h]
  calc N.q₂ * ((Nat.card ↥B₁ * Nat.card ↥B₂) * (Nat.card ↥B₃ * Nat.card ↥B₄))
      ≤ N.q₂ * (Nat.card ↥(R₂ N p ⊓ Subgroup.centralizer {u}) *
          Nat.card ↥(R₂ N p ⊓ Subgroup.centralizer {N.z * u})) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul (hd.card_le h) (hd'.card_le h))
    _ = N.q₂ * Nat.card ↥(R₂ N p ⊓ Subgroup.centralizer {u}) *
          Nat.card ↥(R₂ N p ⊓ Subgroup.centralizer {N.z * u}) := by ring

end CFSG.GH74.GLS.Stage4.Rest.T6

namespace CFSG.GH74.GLS.Stage4.Rest

open Subgroup CFSG.GH74.GLS.Stage4.Hex CFSG.GH74.GLS.Stage4.Rest.T2 CFSG.GH74.GLS.Stage4.Rest.T6

variable {G : Type} [Group G] [Finite G]

theorem allX2_P71Out {N : T2N3 G} {u : G} {p : ℕ} {P₀ P : Subgroup G} (hctx : T6Ctx N u p)
    (hctx' : T6Ctx N.swap u p) (hP₀F : P₀ ≤ N.F) (hP₀p : IsPGroup p ↥P₀)
    (hPeq : P = R₂ N p ⊔ N.X₁) (hRcard : Nat.card ↥(R₂ N p) = N.q₁ ^ 2 * N.q₂ ^ 3)
    (hSyl : ∃ T : Sylow p G, (T : Subgroup G) = P ⊔ P₀) {B₁ B₂ B₃ B₄ : Subgroup G}
    (hd : PairData N.swap p u B₁ B₂) (hd' : PairData N.swap p (N.swap.z * u) B₃ B₄)
    (hc₁ : Nat.card ↥B₁ * Nat.card ↥B₂ = N.q₁ * N.q₂) (hc₂ : Nat.card ↥B₃ * Nat.card ↥B₄ = N.q₁ * N.q₂) :
    Nat.card ↥(R₂ N.swap p) = N.swap.q₁ ^ 2 * N.swap.q₂ ^ 3 ∧
      ∃ P₀' : Subgroup G, P₀' ≤ N.swap.F ∧ IsPGroup p ↥P₀' ∧
        ∃ T : Sylow p G, (T : Subgroup G) = (R₂ N.swap p ⊔ N.swap.X₁) ⊔ P₀' := by
  have : Fact p.Prime := ⟨hctx.prime⟩
  obtain ⟨T₀, hT₀⟩ := hSyl
  have hS := card_RXP hctx hP₀F hP₀p
  have hS' := card_RXP hctx' (show P₀ ≤ N.swap.F from hP₀F) hP₀p
  have hT₀card : Nat.card ↥(T₀ : Subgroup G) = N.q₁ ^ 2 * N.q₂ ^ 3 * N.q₁ * Nat.card ↥P₀ := by
    rw [hT₀, hPeq, hS.2, hRcard]
  have hge := card_R₂_ge hctx' hd hd'
  rw [hc₁, hc₂] at hge
  set m := Nat.card ↥(R₂ N.swap p) with hm
  have hge' : N.q₁ ^ 3 * N.q₂ ^ 2 ≤ m := by
    have : N.swap.q₂ = N.q₁ := rfl
    rw [this] at hge
    calc N.q₁ ^ 3 * N.q₂ ^ 2 = N.q₁ * (N.q₁ * N.q₂ * (N.q₁ * N.q₂)) := by ring
      _ ≤ m := hge
  obtain ⟨Q, hQ⟩ := hS'.1.exists_le_sylow
  have hQcard : Nat.card ↥(Q : Subgroup G) = Nat.card ↥(T₀ : Subgroup G) := by
    rw [Sylow.card_eq_multiplicity Q, Sylow.card_eq_multiplicity T₀]
  have hle : Nat.card ↥((R₂ N.swap p ⊔ N.swap.X₁) ⊔ P₀) ≤ Nat.card ↥(T₀ : Subgroup G) := by
    rw [← hQcard]; exact Subgroup.card_le_of_le hQ
  rw [hS'.2, hT₀card] at hle
  have hq₂ : 0 < N.q₂ := by have := hctx.sec5.loc.q₂_ge; omega
  have hP₀pos : 0 < Nat.card ↥P₀ := Nat.card_pos
  have hle' : m * N.swap.q₁ ≤ N.q₁ ^ 2 * N.q₂ ^ 3 * N.q₁ := by
    have := hle
    exact Nat.le_of_mul_le_mul_right this hP₀pos
  have hle'' : m ≤ N.q₁ ^ 3 * N.q₂ ^ 2 := by
    have h2 : m * N.q₂ ≤ (N.q₁ ^ 3 * N.q₂ ^ 2) * N.q₂ := by
      calc m * N.q₂ = m * N.swap.q₁ := rfl
        _ ≤ N.q₁ ^ 2 * N.q₂ ^ 3 * N.q₁ := hle'
        _ = (N.q₁ ^ 3 * N.q₂ ^ 2) * N.q₂ := by ring
    exact Nat.le_of_mul_le_mul_right h2 hq₂
  have hmeq : m = N.q₁ ^ 3 * N.q₂ ^ 2 := le_antisymm hle'' hge'
  refine ⟨by rw [hmeq]; show _ = N.q₂ ^ 2 * N.q₁ ^ 3; ring, P₀, hP₀F, hP₀p, ?_⟩
  have hSQ : (R₂ N.swap p ⊔ N.swap.X₁) ⊔ P₀ = (Q : Subgroup G) := by
    refine Subgroup.eq_of_le_of_card_ge hQ ?_
    rw [hQcard, hT₀card, hS'.2, hmeq]
    show _ ≤ N.q₁ ^ 3 * N.q₂ ^ 2 * N.q₂ * _
    have : N.q₁ ^ 2 * N.q₂ ^ 3 * N.q₁ = N.q₁ ^ 3 * N.q₂ ^ 2 * N.q₂ := by ring
    rw [this]
  exact ⟨Q, hSQ.symm⟩

end CFSG.GH74.GLS.Stage4.Rest
