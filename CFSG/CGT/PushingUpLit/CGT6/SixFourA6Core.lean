module

public import CFSG.CGT.PushingUpLit.CGT6.SixFourAlt6
public import CFSG.CGT.PushingUpLit.CGT6.SixFourLin

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open scoped commutatorElement

structure A6Setting {Q V : Type} [Group Q] [Finite Q] [Group V] [Finite V] (θ : Q →* MulAut V)
    (J Y₀ : Subgroup Q) : Prop where
  hc : ∀ a b : V, a * b = b * a
  hV : ∀ v : V, v * v = 1
  faithful : Function.Injective θ
  perfect : commutator Q = ⊤
  odd : Odd (Nat.card (Subgroup.center Q))
  alt6 : Nonempty (Q ⧸ Subgroup.center Q ≃* alternatingGroup (Fin 6))
  JY : J ≤ Y₀
  Jcard : Nat.card J = 4
  Jexp : ∀ a ∈ J, a * a = 1
  Y60 : Nat.card Y₀ = 60
  Ygen : ∃ g ∈ Y₀, J ⊔ J.map (MulAut.conj g).toMonoidHom = Y₀
  Ycent : ∀ a ∈ J, a ≠ 1 → ∀ g ∈ Y₀, g * a = a * g → g ∈ J
  Jidx : ∀ a ∈ J, a ≠ 1 → (autFixSub (θ a)).index = 4
  JC : (fixQ θ J).index = 4
  Jquad : ∀ a ∈ J, ∀ v : V, θ a v * v⁻¹ ∈ fixQ θ J
  y3 : ∀ y ∈ Y₀, orderOf y = 3 → 16 ≤ (autFixSub (θ y)).index

section Core

variable {Q V : Type} [Group Q] [Finite Q] [Group V] [Finite V] {θ : Q →* MulAut V}
  {J Y₀ : Subgroup Q}

theorem A6Setting.exists_ne_one (S : A6Setting θ J Y₀) : ∃ a ∈ J, a ≠ 1 := by
  have hne : J ≠ ⊥ := by
    intro h
    have := S.Jcard
    rw [h] at this
    simp at this
  obtain ⟨⟨a, ha⟩, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  exact ⟨a, ha, fun h => ha1 (Subtype.ext h)⟩

theorem A6Setting.index_conj (S : A6Setting θ J Y₀) {a : Q} (ha : a ∈ J) (ha1 : a ≠ 1) {g : Q} :
    (autFixSub (θ (g * a * g⁻¹))).index = 4 := by
  have h1 := index_fixQ_conj θ (Subgroup.zpowers a) g
  rw [fixQ_zpowers] at h1
  have h2 : (Subgroup.zpowers a).map (MulAut.conj g).toMonoidHom = Subgroup.zpowers (g * a * g⁻¹) := by
    rw [MonoidHom.map_zpowers]
    rfl
  rw [h2, fixQ_zpowers] at h1
  rw [h1]
  exact S.Jidx a ha ha1

theorem stabComm_eq_top_of_trivial_center (S : A6Setting θ J Y₀) (hZ : Subgroup.center Q = ⊥) :
    stabComm θ Y₀ = ⊤ := by
  obtain ⟨e₀⟩ := S.alt6
  let e : Q ≃* alternatingGroup (Fin 6) :=
    QuotientGroup.quotientBot.symm.trans ((QuotientGroup.quotientMulEquivOfEq hZ.symm).trans e₀)
  have hc := S.hc
  have hV := S.hV
  have hp3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨y', hy'⟩ := exists_prime_orderOf_dvd_card' (G := Y₀) 3 (by rw [S.Y60]; norm_num)
  set y : Q := (y' : Q) with hy
  have hyY : y ∈ Y₀ := y'.2
  have hyo : orderOf y = 3 := by rw [hy, Subgroup.orderOf_coe]; exact hy'
  obtain ⟨b₁, b₂, t, x, hb₁, hb₂, hb12, ht2, ht1, htb₁, htb₂, hy_cl, hx_cl, hxy_not, hxy, hx3⟩ :=
    alt6_e9_data e hyo
  obtain ⟨a, haJ, ha1⟩ := S.exists_ne_one
  obtain ⟨g, hg⟩ := alt6_involution_conj_abs e (S.Jexp a haJ) ha1 ht2 ht1
  have htidx : (autFixSub (θ t)).index = 4 := by
    rw [← hg]
    exact S.index_conj haJ ha1
  have hθb₁ : θ b₁ ^ 3 = 1 := by rw [← map_pow, hb₁, map_one]
  have hθb₂ : θ b₂ ^ 3 = 1 := by rw [← map_pow, hb₂, map_one]
  have hθb : θ b₁ * θ b₂ = θ b₂ * θ b₁ := by rw [← map_mul, ← map_mul, hb12]
  have hθt₁ : θ t * θ b₁ = θ b₁ ^ 2 * θ t := by rw [← map_mul, ← map_pow, ← map_mul, htb₁]
  have hθt₂ : θ t * θ b₂ = θ b₂ ^ 2 * θ t := by rw [← map_mul, ← map_pow, ← map_mul, htb₂]
  have hcl : ∀ w ∈ Subgroup.closure ({b₁, b₂} : Set Q),
      θ w ∈ Subgroup.closure ({θ b₁, θ b₂} : Set (MulAut V)) := by
    intro w hw
    have := Subgroup.mem_map_of_mem θ hw
    rwa [MonoidHom.map_closure, Set.image_pair] at this
  have hy16 : 16 ≤ (autFixSub (θ y)).index := S.y3 y hyY hyo
  have hxS : x ∈ stabComm θ Y₀ := by
    intro v
    have h := e9t_main hc hV hθb₁ hθb₂ hθb hθt₁ hθt₂ htidx.le (hcl y hy_cl) hy16 (hcl x hx_cl) v
    refine (?_ : autRange hc (θ y) ≤ commSub θ Y₀) h
    rintro _ ⟨w, rfl⟩
    exact mem_commSub_of_mem θ hyY w
  have hxY : x ∉ Y₀ := by
    intro hxY
    have hle : Subgroup.zpowers x ⊔ Subgroup.zpowers y ≤ Y₀ :=
      sup_le (Subgroup.zpowers_le.mpr hxY) (Subgroup.zpowers_le.mpr hyY)
    have hy3 : y ^ 3 = 1 := by rw [← hyo]; exact pow_orderOf_eq_one y
    have hy1 : y ≠ 1 := by
      intro h; rw [h, orderOf_one] at hyo; omega
    have h9 := nine_dvd_card_sup_zpowers hxy hx3 hy3 hy1 hxy_not
    have h60 : Nat.card ↥(Subgroup.zpowers x ⊔ Subgroup.zpowers y) ∣ 60 :=
      S.Y60 ▸ Subgroup.card_dvd_of_le hle
    have := dvd_trans h9 h60
    omega
  have hsup := sup_zpowers_eq_top_of_card_sixty e S.Y60 hxY
  rw [eq_top_iff, ← hsup]
  exact sup_le (le_stabComm θ Y₀) (Subgroup.zpowers_le.mpr hxS)

end Core

end CFSG.CGT.PushingUpLit.CGT6
