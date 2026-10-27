module

public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8E7Torus
public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8E8Aut
public import CFSG.Timmesfeld.Orders.Distinct
public import CFSG.Timmesfeld.Orders.Classical
import all CFSG.Timmesfeld.Orders.Distinct

public section

namespace CFSG.ComponentClassification.RankTwoExceptional.E7Sec8

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.SeitzReduction (highRoot isRoot_highRoot)
open CFSG.Open (ordD ordE7)

variable {K : Type} [Field K]

theorem odd_card_e7T
    [Finite K] {m : ℕ} (hm : 1 ≤ m) (hK : Nat.card K = 2 ^ m) :
    Odd (Nat.card (e7T K)) := by
  have : Finite (ModGL .E7 K) := finite_modGL
  exact E8.odd_card_of_forall_pow_eq_one (E8.odd_card_units_e8 hm hK) fun g =>
    Subtype.ext (Subtype.ext (by
      rw [Subgroup.coe_pow, Subgroup.coe_pow, Subgroup.coe_one, Subgroup.coe_one]
      exact pow_card_units_eq_one_of_mem_torusGroup_e7 g.2))

theorem e7_leviData
    [Finite K] {m : ℕ} (hm : 1 ≤ m) (hK : Nat.card K = 2 ^ m) (hq : 2 < 2 ^ m)
    {Z : Subgroup (adjointGroup .E7 K)} (hZ : Z ≤ e7L K) :
    Exc.LeviData Z (e7D K) (e7Q K) (e7T K) (e7L K) where
  D_perfect := commutator_e7D (E8.four_le_card_e8 hK hq)
  D_le := e7D_le_centralizer_e7L.trans (Subgroup.centralizer_le hZ)
  Q_le := e7Q_le_e7D
  Q_ne_bot := e7Q_ne_bot hK hq
  odd_Q := odd_card_e7Q hm hK
  Q_le_H := e7Q_le_e7T
  H_comm := e7T_comm
  H_le := e7T_le_normalizer_e7L
  L_le := e7L_le_centralizer_e7Q
  cent_eq := exists_mem_e7T_inv_mul_mem_e7L hK hq
  quasisimple := (e7L_recognition hm hK).1
  odd_center := odd_card_center_e7L hm hK
  Z_le := hZ

theorem not_ordD_dvd_ordE7 {e : ℕ} (he : 1 ≤ e) : ¬ ordD 6 (2 ^ (2 * e)) ∣ ordE7 (2 ^ e) := by
  obtain ⟨p, hp⟩ := CFSG.Timmesfeld.exists_isPrimitivePrimeDivisor (k := 20 * e) (by omega)
    (by omega)
  have h1 : p ∣ ordD 6 (2 ^ (2 * e)) :=
    ((CFSG.Timmesfeld.Orders.profile_ordD (n := 6) (f := 2 * e) (by norm_num)
      (by omega)).prim p (20 * e) hp (by omega)).2 (by
        unfold CFSG.Timmesfeld.Orders.zD
        exact Or.inr ⟨5, by simp, ⟨1, by ring⟩⟩)
  have h2 : ¬ p ∣ ordE7 (2 ^ e) := fun h => by
    have hz := ((CFSG.Timmesfeld.Orders.profile_ordE7 he).prim p (20 * e) hp (by omega)).1 h
    unfold CFSG.Timmesfeld.Orders.zE7 CFSG.Timmesfeld.Orders.zList at hz
    obtain ⟨a, ha, hd⟩ := hz
    have hle : ∀ a ∈ [18, 14, 12, 10, 8, 6, 2], 0 < a ∧ a < 20 := by decide
    obtain ⟨ha0, ha20⟩ := hle a ha
    have h3 := Nat.le_of_dvd (Nat.mul_pos (by omega) ha0) hd
    have h4 : e * a < 20 * e := by nlinarith
    omega
  exact fun hd => h2 (h1.trans hd)

theorem card_quot_e7L
    [Finite K] {m : ℕ} (hm : 1 ≤ m) (hK : Nat.card K = 2 ^ m) :
    Nat.card (↥(e7L K) ⧸ Subgroup.center ↥(e7L K)) = ordD 6 (2 ^ m) :=
  (CFSG.Timmesfeld.card_statedClassicalModel_two
    (statedClassicalModel_of_lieModel_POmegaPlus (e7L_recognition hm hK).2)).2.2.2.1 rfl

theorem e7_autFix
    [Finite K] {m : ℕ} (hm : 1 ≤ m) (hK : Nat.card K = 2 ^ m) (hq : 2 < 2 ^ m) :
    Exc.AutFix (e7Q K) (e7L K) := by
  classical
  have hZ : Subgroup.center (adjointGroup .E7 K) = ⊥ := center_adjointGroup_eq_bot
  have hL := e7_leviData hm hK hq (Z := ⊥) bot_le
  have hHodd := odd_card_e7T hm hK
  obtain ⟨hNF, Θ, hΘ, -, hker, hinv⟩ :=
    even_E7_E8_exact_inner_field_automorphism_normal_form hm K hK .E7 (Or.inl rfl)
  have hinner : ∀ β : MulAut (adjointGroup .E7 K),
      β ∈ (MulAut.conj : adjointGroup .E7 K →* MulAut (adjointGroup .E7 K)).range →
      (∃ j : ℕ, β ^ 2 ^ j = 1) → (∀ y ∈ e7Q K, β y = y) → (∀ y ∈ e7L K, β y = y) →
        β = 1 := by
    rintro β ⟨c, rfl⟩ ⟨j, hj⟩ hβQ hβL
    rw [D4.conj_eq_one_of_fix_d4 hZ hL hHodd hj hβQ hβL, map_one]
  intro α ⟨k, hk⟩ hQ hLf
  have hfix : ∀ S : Subgroup (adjointGroup .E7 K), (∀ y ∈ S, α y = y) →
      ∀ n : ℕ, ∀ y ∈ S, (α ^ n) y = y := by
    intro S hS n
    induction n with
    | zero => intro y _; rfl
    | succ n ih => intro y hy; rw [pow_succ, MulAut.mul_apply, hS y hy, ih y hy]
  have hpow2 : ∀ n : ℕ, ∃ j : ℕ, (α ^ n) ^ 2 ^ j = 1 :=
    fun n => ⟨k, by rw [← pow_mul, mul_comm, pow_mul, hk, one_pow]⟩
  have hex : ∃ j, α ^ 2 ^ j ∈
      (MulAut.conj : adjointGroup .E7 K →* MulAut (adjointGroup .E7 K)).range :=
    ⟨k, by rw [hk]; exact one_mem _⟩
  rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
  · have hα := Nat.find_spec hex
    rw [h0, pow_zero, pow_one] at hα
    exact hinner α hα ⟨k, hk⟩ hQ hLf
  exfalso
  obtain ⟨j, hj⟩ : ∃ j, Nat.find hex = j + 1 := ⟨Nat.find hex - 1, by omega⟩
  have hβo : α ^ 2 ^ j ∉
      (MulAut.conj : adjointGroup .E7 K →* MulAut (adjointGroup .E7 K)).range :=
    Nat.find_min hex (by omega)
  have hβ2' : (α ^ 2 ^ j) ^ 2 ∈
      (MulAut.conj : adjointGroup .E7 K →* MulAut (adjointGroup .E7 K)).range := by
    rw [← pow_mul, ← pow_succ, ← hj]
    exact Nat.find_spec hex
  have hβ2 : (α ^ 2 ^ j) ^ 2 = 1 := by
    rw [← pow_mul]
    exact hinner _ (by rw [pow_mul]; exact hβ2') (hpow2 _) (hfix _ hQ _) (hfix _ hLf _)
  have hβL : ∀ y ∈ e7L K, (α ^ 2 ^ j) y = y := hfix _ hLf _
  obtain ⟨⟨g, σ⟩, hgσ, -⟩ := hNF (α ^ 2 ^ j)
  have hΘβ : Θ (α ^ 2 ^ j) = σ := hΘ _ g σ hgσ
  have hσ1 : Θ (α ^ 2 ^ j) ≠ 1 := fun h1 => hβo (by
    rw [← MonoidHom.mem_ker, hker] at h1
    exact h1)
  obtain ⟨⟨e, he⟩, hσc⟩ := (hinv _ hβ2).resolve_left hσ1
  rw [hΘβ] at hσc
  have he1 : 1 ≤ e := by omega
  have hK' : Nat.card K = 2 ^ (2 * e) := by rw [hK, he, two_mul]
  have hσ' : ∀ c, σ c = c ^ 2 ^ e := fun c => by rw [hσc, show m / 2 = e by omega]
  obtain ⟨hQ1, -⟩ :=
    even_exceptional_quadratic_field_graph_field_involution_descent he1 K hK' σ.toRingHom hσ'
  obtain ⟨β₀, hβ₀, hdesc⟩ := hQ1 .E7
  obtain ⟨-, hdα⟩ := hdesc g fun _ => 1
  have hβform : ∀ u, ((α ^ 2 ^ j) u : ModGL .E7 K) = (g : ModGL .E7 K) *
      rootDiagUnit .E7 (fun _ => 1) * Units.map (entrywiseHom σ.toRingHom) (u : ModGL .E7 K) *
        (rootDiagUnit .E7 fun _ => 1)⁻¹ * (g : ModGL .E7 K)⁻¹ := by
    intro u
    rw [show (fun _ => (1 : Kˣ)) = (1 : Fin Tag.E7.rank → Kˣ) from rfl, rootDiagUnit_one, mul_one,
      inv_one, mul_one]
    exact hgσ u
  obtain ⟨ψ, -, hfixψ, -⟩ := hdα (α ^ 2 ^ j) hβform (by rw [← pow_two]; exact hβ2)
  have hβ₀e : β₀ = entrywiseAdjointAut .E7 σ :=
    MulEquiv.ext fun u => Subtype.ext (by rw [hβ₀ u, coe_entrywiseAdjointAut])
  obtain ⟨-, -, -, hmap, ⟨-, -, -, hmodel, -⟩, -⟩ :=
    even_E7_E8_canonical_field_full_centralizer .E7 (Or.inl rfl) he1 K hK' σ hσ'
  have hcard1 : Nat.card (e7L K) ∣
      Nat.card ((α ^ 2 ^ j).toMonoidHom.eqLocus (MonoidHom.id (adjointGroup .E7 K))) :=
    Subgroup.card_dvd_of_le fun y hy => hβL y hy
  have hcard2 : Nat.card ((α ^ 2 ^ j).toMonoidHom.eqLocus (MonoidHom.id (adjointGroup .E7 K))) =
      Nat.card (fixedFieldImage .E7 σ) := by
    rw [← hmap, Subgroup.card_map_of_injective (adjointGroup .E7 K).subtype_injective, ← hβ₀e,
      ← hfixψ, Subgroup.card_map_of_injective ψ.injective]
  obtain ⟨K₀, _, _, hK₀, ⟨E⟩⟩ := nonempty_mulEquiv_adjointGroup .E7 (hmodel rfl).2
  have hcard3 : Nat.card (fixedFieldImage .E7 σ) = Nat.card (adjointGroup .E7 K₀) :=
    Nat.card_congr E.toEquiv
  have hcard4 : Nat.card (adjointGroup .E7 K₀) = ordE7 (2 ^ e) := by
    rw [CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_E7, hK₀]
  have hcard5 : ordD 6 (2 ^ (2 * e)) ∣ Nat.card (e7L K) := by
    rw [show 2 * e = m by omega, ← card_quot_e7L hm hK]
    exact Subgroup.card_quotient_dvd_card _
  have hfin : Nat.card ((α ^ 2 ^ j).toMonoidHom.eqLocus (MonoidHom.id (adjointGroup .E7 K))) =
      ordE7 (2 ^ e) := by
    rw [hcard2, hcard3, hcard4]
  exact not_ordD_dvd_ordE7 he1 ((hcard5.trans hcard1).trans (dvd_of_eq hfin))

end CFSG.ComponentClassification.RankTwoExceptional.E7Sec8
