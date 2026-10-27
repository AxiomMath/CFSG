module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Ctx10
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Ctx11

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec8

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm3.Sec6
open scoped commutatorElement Pointwise

namespace Setup8

variable {G : Type} [Group G] [Finite G] {z : G} {S K₁ K₂ W₁ W₂ U : Subgroup G} {u h : G}

theorem cent_Q₁_le_W₁ (hII : II4_4_4_center) (hq : II4_4_quat) (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h)
    {x : G} (hxQ : x ∈ Qof S K₁) (hc : ∀ a ∈ Vof S K₂ W₁, x * a = a * x) : x ∈ W₁ :=
  (hs.gq_Q₁ hII).mem_of_commute hs.W₁_le_Q₁ hs.W₁_max.2.1 (hs.relIndex_W₁ hII)
    (inf_le_left : Vof S K₂ W₁ ≤ W₁) (hs.four_le_V₂ hII hq) hxQ hc

theorem W₁_card (hII : II4_4_4_center) (hq : II4_4_quat) (hrec : Bg.B_reciprocity)
    (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) {k : ℕ} (hk : Nat.card ↥(Vof S K₁ W₂) = 2 ^ k) :
    ∃ e : ℕ, (e = 1 ∨ e = 2) ∧ Nat.card ↥W₁ = e * 2 ^ k := by
  obtain ⟨e, he, hW⟩ := hs.W₂_card hII hq hrec hk
  refine ⟨e, he, ?_⟩
  obtain ⟨e', he', -, hNN, hq1, hq2⟩ := hs.lemma82_core hII hq hrec
  have h1 := hs.card_W₁ hII
  have h2 := hs.card_W₂ hII
  have hQQ : Nat.card ↥(Qof S K₁) = Nat.card ↥(Qof S K₂) := by rw [hq1, hq2, hNN]
  omega

theorem W₁_pow (hII : II4_4_4_center) (hq : II4_4_quat) (hrec : Bg.B_reciprocity)
    (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) {k : ℕ} (hk : Nat.card ↥(Vof S K₁ W₂) = 2 ^ k) :
    ∀ w ∈ W₁, w ^ (2 ^ (k + 1)) = 1 := by
  intro w hw
  obtain ⟨e, he, hW⟩ := hs.W₁_card hII hq hrec hk
  have h1 := Basic.pow_card_of_mem hw
  have hdvd : Nat.card ↥W₁ ∣ 2 ^ (k + 1) := by
    rw [hW]
    rcases he with rfl | rfl
    · rw [one_mul]; exact pow_dvd_pow 2 (Nat.le_succ k)
    · exact ⟨1, by ring⟩
  exact orderOf_dvd_iff_pow_eq_one.1 ((orderOf_dvd_of_pow_eq_one h1).trans hdvd)

theorem W₁_sq_mem (hII : II4_4_4_center) (hq : II4_4_quat) (hrec : Bg.B_reciprocity)
    (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) {k : ℕ} (hk : Nat.card ↥(Vof S K₁ W₂) = 2 ^ k) :
    ∀ w ∈ W₁, w * w ∈ Vof S K₂ W₁ := by
  intro w hw
  refine Basic.mem_of_pow_card_eq_one (V := Vof S K₂ W₁) hs.W₁_max.2.1 inf_le_left (mul_mem hw hw) ?_
  rw [hs.V₂_card_eq hII hq hrec hk, ← pow_two, ← pow_mul, show 2 * 2 ^ k = 2 ^ (k + 1) by ring]
  exact hs.W₁_pow hII hq hrec hk w hw

theorem W₁_val (hII : II4_4_4_center) (hq : II4_4_quat) (hrec : Bg.B_reciprocity)
    (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) {k : ℕ} (hk : Nat.card ↥(Vof S K₁ W₂) = 2 ^ k) :
    ∀ w ∈ W₁, w ^ (2 ^ k) = 1 ∨ w ^ (2 ^ k) = z := by
  intro w hw
  have hw2 : w ^ (2 ^ k) * w ^ (2 ^ k) = 1 := by
    rw [← pow_add, show 2 ^ k + 2 ^ k = 2 ^ (k + 1) by ring]
    exact hs.W₁_pow hII hq hrec hk w hw
  exact (hs.gq_Q₁ hII).uniq _ (pow_mem (hs.W₁_le_Q₁ hw) _) hw2

theorem W₂_val (hII : II4_4_4_center) (hq : II4_4_quat) (hrec : Bg.B_reciprocity)
    (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) {k : ℕ} (hk : Nat.card ↥(Vof S K₁ W₂) = 2 ^ k) :
    ∀ w ∈ W₂, w ^ (2 ^ k) = 1 ∨ w ^ (2 ^ k) = z := by
  intro w hw
  have hw2 : w ^ (2 ^ k) * w ^ (2 ^ k) = 1 := by
    rw [← pow_add, show 2 ^ k + 2 ^ k = 2 ^ (k + 1) by ring]
    exact hs.W₂_pow hII hq hrec hk w hw
  exact (hs.gq_Q₂ hII).uniq _ (pow_mem (hs.W₂_le_Q₂ hw) _) hw2

theorem decomp_e2 (hII : II4_4_4_center) (hq : II4_4_quat) (hrec : Bg.B_reciprocity)
    (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) (he : (Pz S z).relIndex (S1 S K₁) = 4) {k : ℕ} (hk2 : 2 ≤ k)
    (hk : Nat.card ↥(Vof S K₁ W₂) = 2 ^ k) {x : G} (hxS : x ∈ S)
    (hx1 : ∀ a ∈ Vof S K₁ W₂, x * a = a * x) (hx2 : ∀ a ∈ Vof S K₂ W₁, x * a = a * x) :
    ∃ q₁ ∈ W₁, ∃ q₂ ∈ W₂, x = q₁ * q₂ ∧ x ^ (2 ^ k) = q₁ ^ (2 ^ k) * q₂ ^ (2 ^ k) := by
  have hxS1 : x ∈ S1 S K₁ := hs.cent_le_S1 hII hq hxS hx1
  obtain ⟨-, hS1eq⟩ := hs.fused.p66.2.2.2 he
  obtain ⟨hN₂, -⟩ := hs.nc_quot (K := K₂) (Or.inr rfl)
  obtain ⟨hN₁, -⟩ := hs.nc_quot (K := K₁) (Or.inl rfl)
  have hnorm₂ : S1 S K₁ ≤ normalizer (Qof S K₂ : Set G) :=
    normalizer_of_normal_subgroupOf (hs.Q₂_le_S1 hII) hN₂
  have hnorm₁ : S1 S K₁ ≤ normalizer (Qof S K₁ : Set G) :=
    normalizer_of_normal_subgroupOf hs.Q₁_le_S1 hN₁
  have hx' : x ∈ Qof S K₁ ⊔ Qof S K₂ := by rw [← hS1eq]; exact hxS1
  obtain ⟨a, haQ, b, hbQ, hxab⟩ :=
    Basic.mem_sup_of_le_normalizer' (hs.Q₁_le_S1.trans hnorm₂) hx'
  have ha_comm : ∀ c ∈ Vof S K₁ W₂, a * c = c * a :=
    fun c hc => hs.Q_comm_P hII (Or.inl rfl) a haQ c hc.2
  have hb_comm : ∀ c ∈ Vof S K₂ W₁, b * c = c * b :=
    fun c hc => hs.Q_comm_P hII (Or.inr rfl) b hbQ c hc.2
  have hbW : b ∈ W₂ := by
    apply hs.cent_Q₂_le_W₂ hII hq hbQ
    intro c hc
    have h1 := hx1 c hc
    rw [hxab] at h1
    have h2 := ha_comm c hc
    calc b * c = a⁻¹ * (a * b * c) := by group
      _ = a⁻¹ * (c * (a * b)) := by rw [h1]
      _ = a⁻¹ * (c * a) * b := by group
      _ = a⁻¹ * (a * c) * b := by rw [h2]
      _ = c * b := by group
  have haW : a ∈ W₁ := by
    apply hs.cent_Q₁_le_W₁ hII hq haQ
    intro c hc
    have h1 := hx2 c hc
    rw [hxab] at h1
    have h2 := hb_comm c hc
    have h3 : (a * c) * b = (c * a) * b := by
      calc (a * c) * b = a * (c * b) := by group
        _ = a * (b * c) := by rw [h2]
        _ = a * b * c := by group
        _ = c * (a * b) := h1
        _ = (c * a) * b := by group
    exact mul_right_cancel h3
  have hcomm_mem : b * a * b⁻¹ * a⁻¹ ∈ zpowers z := by
    have h1 : b * a * b⁻¹ * a⁻¹ ∈ Qof S K₁ := by
      have h0 : b * a * b⁻¹ ∈ Qof S K₁ :=
        (Subgroup.mem_normalizer_iff.1 (hnorm₁ (hs.Q₂_le_S1 hII hbQ)) a).1 haQ
      exact mul_mem h0 (inv_mem haQ)
    have h2 : b * a * b⁻¹ * a⁻¹ ∈ Qof S K₂ := by
      have h0 : a * b⁻¹ * a⁻¹ ∈ Qof S K₂ :=
        (Subgroup.mem_normalizer_iff.1 (hnorm₂ (hs.Q₁_le_S1 haQ)) b⁻¹).1 (inv_mem hbQ)
      have e : b * a * b⁻¹ * a⁻¹ = b * (a * b⁻¹ * a⁻¹) := by group
      rw [e]; exact mul_mem hbQ h0
    have h3 : b * a * b⁻¹ * a⁻¹ ∈ Qof S K₁ ⊓ Qof S K₂ := ⟨h1, h2⟩
    rwa [hs.Q_inf_Q hII] at h3
  obtain ⟨c, hc, hcdef⟩ : ∃ c, (c = 1 ∨ c = z) ∧ b * a * b⁻¹ * a⁻¹ = c :=
    ⟨_, (M.mem_zpowers_of_sq hs.z_sq).1 hcomm_mem, rfl⟩
  have hc2 : c * c = 1 := by
    rcases hc with rfl | rfl
    · simp
    · exact hs.z_sq
  have hcS : ∀ y ∈ S, c * y = y * c := by
    intro y hy
    rcases hc with rfl | rfl
    · simp
    · exact hs.z_comm hII hy
  have haS : a ∈ S := haQ.1
  have hbS : b ∈ S := hbQ.1
  have hqv : b * a * b⁻¹ = a * c := by
    have e : b * a * b⁻¹ = c * a := by
      calc b * a * b⁻¹ = (b * a * b⁻¹ * a⁻¹) * a := by group
        _ = c * a := by rw [hcdef]
    rw [e]; exact hcS a haS
  have hsq : a * a ∈ Vof S K₂ W₁ := hs.W₁_sq_mem hII hq hrec hk a haW
  have h1 : Commute (a * a) b := (hs.Q_comm_P hII (Or.inr rfl) b hbQ _ hsq.2).symm
  have h2 : Commute c b := hcS b hbS
  have h3 : Commute (a * a) c := (hcS (a * a) (mul_mem haS haS)).symm
  have hpow := Basic.pow_two_pow_mul_gen hk2 hc2 hqv h1 h2 h3
  refine ⟨a, haW, b, hbW, hxab, ?_⟩
  rw [hxab]
  exact hpow

theorem KL_e2 (hII : II4_4_4_center) (hq : II4_4_quat) (hrec : Bg.B_reciprocity)
    (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) {k : ℕ} (hk2 : 2 ≤ k)
    (hk : Nat.card ↥(Vof S K₁ W₂) = 2 ^ k) (he : (Pz S z).relIndex (S1 S K₁) = 4) {x : G}
    (hxS : x ∈ S) (hx1 : ∀ a ∈ Vof S K₁ W₂, x * a = a * x)
    (hx2 : ∀ a ∈ Vof S K₂ W₁, x * a = a * x) (hxk : x ^ (2 ^ k) = 1) : x ∈ Aof S K₁ W₂ h := by
  have hV₂A := hs.V₂_le_A hII hq hrec hk
  have hV₁A : Vof S K₁ W₂ ≤ Aof S K₁ W₂ h := le_sup_left
  have hVA : conjugate (Vof S K₁ W₂) h ≤ Aof S K₁ W₂ h := le_sup_right
  have hAne := hs.A_ne_V₁V₂ hII hq hrec hk2 hk
  have hV₂card := hs.V₂_card_eq hII hq hrec hk
  obtain ⟨g, hgV, hg⟩ : ∃ g ∈ conjugate (Vof S K₁ W₂) h, g ∉ Vof S K₁ W₂ ⊔ Vof S K₂ W₁ := by
    by_contra hcon
    push Not at hcon
    apply hAne
    apply le_antisymm
    · exact sup_le le_sup_left (fun g hg => hcon g hg)
    · exact sup_le hV₁A hV₂A
  have hgS : g ∈ S := (hs.V₁h_le_S1 hII hq hrec hgV).1
  have hg1 : ∀ a ∈ Vof S K₁ W₂, g * a = a * g :=
    fun a ha => (hs.V₁V_comm hII hq hrec a ha g hgV).symm
  have hg2 : ∀ a ∈ Vof S K₂ W₁, g * a = a * g :=
    fun a ha => (hs.V₂V_comm hII hq hrec a ha g hgV).symm
  have hgk : g ^ (2 ^ k) = 1 := hs.V_pow hk g hgV
  obtain ⟨g₁, hg₁, g₂, hg₂, hgdef, hgpow⟩ := hs.decomp_e2 hII hq hrec he hk2 hk hgS hg1 hg2
  obtain ⟨q₁, hq₁, q₂, hq₂, hxdef, hxpow⟩ := hs.decomp_e2 hII hq hrec he hk2 hk hxS hx1 hx2
  have hz1 : z⁻¹ = z := inv_eq_of_mul_eq_one_right hs.z_sq
  have hpair : ∀ p r : G, (p = 1 ∨ p = z) → (r = 1 ∨ r = z) → p * r = 1 →
      (p = 1 ∧ r = 1) ∨ (p = z ∧ r = z) := by
    intro p r hp hr hpr
    rcases hp with rfl | rfl <;> rcases hr with rfl | rfl
    · exact Or.inl ⟨rfl, rfl⟩
    · exfalso; apply hs.z_ne; simpa using hpr
    · exfalso; apply hs.z_ne; simpa using hpr
    · exact Or.inr ⟨rfl, rfl⟩
  have hcg := hpair _ _ (hs.W₁_val hII hq hrec hk g₁ hg₁) (hs.W₂_val hII hq hrec hk g₂ hg₂)
    (by rw [← hgpow]; exact hgk)
  have hcx := hpair _ _ (hs.W₁_val hII hq hrec hk q₁ hq₁) (hs.W₂_val hII hq hrec hk q₂ hq₂)
    (by rw [← hxpow]; exact hxk)
  have hmem₁ : ∀ w ∈ W₁, w ^ (2 ^ k) = 1 → w ∈ Vof S K₂ W₁ := fun w hw hw1 =>
    Basic.mem_of_pow_card_eq_one (V := Vof S K₂ W₁) hs.W₁_max.2.1 inf_le_left hw
      (by rw [hV₂card]; exact hw1)
  have hmem₂ : ∀ w ∈ W₂, w ^ (2 ^ k) = 1 → w ∈ Vof S K₁ W₂ := fun w hw hw1 =>
    Basic.mem_of_pow_card_eq_one (V := Vof S K₁ W₂) hs.W₂_max.2.1 inf_le_left hw
      (by rw [hk]; exact hw1)
  have hgz : g₁ ^ (2 ^ k) = z ∧ g₂ ^ (2 ^ k) = z := by
    rcases hcg with ⟨h1, h2⟩ | h
    · exfalso
      apply hg
      rw [hgdef]
      have : g₁ * g₂ ∈ Vof S K₂ W₁ ⊔ Vof S K₁ W₂ :=
        Subgroup.mul_mem_sup (hmem₁ g₁ hg₁ h1) (hmem₂ g₂ hg₂ h2)
      rwa [sup_comm] at this
    · exact h
  rcases hcx with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [hxdef]
    exact mul_mem (hV₂A (hmem₁ q₁ hq₁ h1)) (hV₁A (hmem₂ q₂ hq₂ h2))
  ·
    have hcomm₁ : Commute q₁ g₁⁻¹ :=
      show q₁ * g₁⁻¹ = g₁⁻¹ * q₁ from Basic.cyclic_comm hs.W₁_max.2.1 q₁ hq₁ g₁⁻¹ (inv_mem hg₁)
    have hcomm₂ : Commute q₂ g₂⁻¹ :=
      show q₂ * g₂⁻¹ = g₂⁻¹ * q₂ from Basic.cyclic_comm hs.W₂_max.2.1 q₂ hq₂ g₂⁻¹ (inv_mem hg₂)
    have hr₁ : q₁ * g₁⁻¹ ∈ Vof S K₂ W₁ := by
      apply hmem₁ _ (mul_mem hq₁ (inv_mem hg₁))
      rw [hcomm₁.mul_pow, inv_pow, h1, hgz.1, hz1]
      exact hs.z_sq
    have hr₂ : q₂ * g₂⁻¹ ∈ Vof S K₁ W₂ := by
      apply hmem₂ _ (mul_mem hq₂ (inv_mem hg₂))
      rw [hcomm₂.mul_pow, inv_pow, h2, hgz.2, hz1]
      exact hs.z_sq
    have hcomm : g₁ * (q₂ * g₂⁻¹) = (q₂ * g₂⁻¹) * g₁ :=
      hs.Q_comm_P hII (Or.inl rfl) g₁ (hs.W₁_le_Q₁ hg₁) _ hr₂.2
    have hx_eq : x = (q₁ * g₁⁻¹) * (q₂ * g₂⁻¹) * g := by
      rw [hxdef, hgdef]
      calc q₁ * q₂ = (q₁ * g₁⁻¹) * (g₁ * (q₂ * g₂⁻¹)) * g₂ := by group
        _ = (q₁ * g₁⁻¹) * ((q₂ * g₂⁻¹) * g₁) * g₂ := by rw [hcomm]
        _ = (q₁ * g₁⁻¹) * (q₂ * g₂⁻¹) * (g₁ * g₂) := by group
    rw [hx_eq]
    exact mul_mem (mul_mem (hV₂A hr₁) (hV₁A hr₂)) (hVA hgV)

theorem A_normedBy_S_e2 (hII : II4_4_4_center) (hq : II4_4_quat) (hrec : Bg.B_reciprocity)
    (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) (he : (Pz S z).relIndex (S1 S K₁) = 4) {k : ℕ} (hk2 : 2 ≤ k)
    (hk : Nat.card ↥(Vof S K₁ W₂) = 2 ^ k) : NormedBy (Aof S K₁ W₂ h) S := by
  obtain ⟨e, he', hri, hNN, hq1, hq2⟩ := hs.lemma82_core hII hq hrec
  have h8 : 8 ≤ Nat.card ↥(Pof S K₁) := (hs.gq_P hII hq (Or.inl rfl)).eight_le_card
  have h16 : 16 ≤ Nat.card ↥(Qof S K₁) := by
    rcases he' with rfl | rfl
    · omega
    · omega
  exact hs.A_normedBy_S_of hII hq hrec hk2 hk (fun t ht hn => hs.swap_V hII hq hrec h16 ht hn)
    (fun x hxS hx1 hx2 hxk => hs.KL_e2 hII hq hrec hk2 hk he hxS hx1 hx2 hxk)

end Setup8

end CFSG.GH74.GLS.Stage1.Thm3.Sec8
