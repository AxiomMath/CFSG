module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3A6Case2Core

@[expose] public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3A6Setup

open CFSG.Open CFSG.ABGLocalTools CFSG.Quasithin Subgroup
  CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3A6Aux CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3A6Core
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem exists_isMaxElemAbelian (Y : Subgroup G) : ∃ A : Subgroup G, IsMaxElemAbelian Y A := by
  have hfin : Finite (Subgroup G) := Finite.of_injective _ SetLike.coe_injective
  obtain ⟨A, hA, hmax⟩ := Set.exists_max_image
    {B : Subgroup G | B ≤ Y ∧ IsElemAbelian 2 B} (fun B => Nat.card B) (Set.toFinite _)
    ⟨⊥, bot_le, ⟨inferInstance, fun x hx => by rw [mem_bot.mp hx]; group⟩⟩
  exact ⟨A, hA.1, hA.2, fun B hB hBel => hmax B ⟨hB, hBel⟩⟩

theorem thompsonJ_ne_bot {Y : Subgroup G} (hY2 : IsPGroup 2 Y) (hYne : Y ≠ ⊥) :
    thompsonJ Y ≠ ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨A, hA⟩ := exists_isMaxElemAbelian Y
  have hcard : 2 ≤ Nat.card A := by
    haveI : Nontrivial Y := (Subgroup.nontrivial_iff_ne_bot Y).mpr hYne
    have hdvd : 2 ∣ Nat.card Y := by
      rcases hY2.card_eq_or_dvd with h | h
      · exact absurd (Subgroup.eq_bot_of_card_eq Y h) hYne
      · exact h
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 2 hdvd
    have hz2 : (z : G) ^ 2 = 1 := by
      have := pow_orderOf_eq_one z
      rw [hz] at this
      simpa using congrArg Subtype.val this
    have hz1 : (z : G) ≠ 1 := by
      intro h1
      have : z = 1 := Subtype.ext h1
      rw [this, orderOf_one] at hz
      exact absurd hz (by norm_num)
    have hel : IsElemAbelian 2 (zpowers (z : G)) := by
      refine ⟨IsMulCommutative.of_setLike_mul_comm fun a ha b hb => ?_, fun w hw => ?_⟩
      · obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp ha
        obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hb
        exact ((Commute.refl (z : G)).zpow_zpow i j).eq
      · obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hw
        rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hz2, one_zpow]
    have hle : zpowers (z : G) ≤ Y := zpowers_le.mpr z.2
    have h1 := hA.2.2 _ hle hel
    have h2 : Nat.card (zpowers (z : G)) = 2 := by
      rw [Nat.card_zpowers, orderOf_eq_prime hz2 hz1]
    omega
  intro hbot
  have hAle : A ≤ thompsonJ Y := le_iSup₂_of_le A hA le_rfl
  rw [hbot, le_bot_iff] at hAle
  rw [hAle] at hcard
  simp at hcard

theorem isMaxElemAbelian_conj {Y A : Subgroup G} (hA : IsMaxElemAbelian Y A) (g : G) :
    IsMaxElemAbelian (Y.map (MulAut.conj g).toMonoidHom) (A.map (MulAut.conj g).toMonoidHom) := by
  refine ⟨Subgroup.map_mono hA.1, isElemAbelian_conj hA.2.1 g, fun B hB hBel => ?_⟩
  have hB' : B.map (MulAut.conj g⁻¹).toMonoidHom ≤ Y := by
    rintro _ ⟨b, hb, rfl⟩
    obtain ⟨y, hy, hyb⟩ := hB hb
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hyb ⊢
    rw [← hyb]
    have : g⁻¹ * (g * y * g⁻¹) * g⁻¹⁻¹ = y := by group
    rw [this]
    exact hy
  have h1 := hA.2.2 _ hB' (isElemAbelian_conj hBel g⁻¹)
  rw [Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective] at h1
  rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
  exact h1

section Frame

variable {M O : Subgroup G} {x e₂ e₃ t ρ : G} {s : ℤ} (hf : A6VIFrame M O x e₂ e₃ t ρ s)

include hf

theorem t_mem_normalizer_Q : t ∈ normalizer ((Qf x e₂ e₃ : Subgroup G) : Set G) := by
  apply mem_normalizer_of_map_le
  rw [Subgroup.map_sup, Subgroup.map_sup]
  refine sup_le ?_ (sup_le ?_ ?_)
  · rw [MonoidHom.map_zpowers]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [hf.t_x]
    exact le_sup_of_le_right (le_sup_left)
  · rw [MonoidHom.map_zpowers]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [hf.t_e₂]
    exact le_sup_of_le_right (le_sup_right)
  · rw [MonoidHom.map_zpowers]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [hf.t_e₃]
    exact le_sup_left

theorem ρ_mem_normalizer_Q : ρ ∈ normalizer ((Qf x e₂ e₃ : Subgroup G) : Set G) := by
  apply mem_normalizer_of_map_le
  rw [Subgroup.map_sup, Subgroup.map_sup]
  refine sup_le ?_ (sup_le ?_ ?_)
  · rw [MonoidHom.map_zpowers]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [hf.ρ_x]
    exact le_sup_left
  · rw [MonoidHom.map_zpowers]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [hf.ρ_e₂]
    exact le_sup_of_le_right (le_sup_of_le_right (zpowers_le.mpr (zpow_mem_zpowers e₃ s)))
  · rw [MonoidHom.map_zpowers]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [hf.ρ_e₃]
    exact le_sup_of_le_right (le_sup_of_le_left (zpowers_le.mpr (zpow_mem_zpowers e₂ (-s))))

theorem frame_replace {t' ρ' : G} (ht' : t' ∈ M)
    (htx : t' * x * t'⁻¹ = e₂) (hte₂ : t' * e₂ * t'⁻¹ = e₃) (hte₃ : t' * e₃ * t'⁻¹ = x)
    (hρ' : ρ' ∈ M) (hρx : ρ' * x * ρ'⁻¹ = x) (hρe₂ : ρ' * e₂ * ρ'⁻¹ = e₃ ^ s)
    (hρe₃ : ρ' * e₃ * ρ'⁻¹ = e₂ ^ (-s)) : A6VIFrame M O x e₂ e₃ t' ρ' s :=
  { toVITriple := hf.toVITriple, O_le := hf.O_le, O_norm := hf.O_norm, O_cop := hf.O_cop,
    O₂_le := hf.O₂_le, O₂_ne := hf.O₂_ne, charTwo := hf.charTwo, D1 := hf.D1,
    x_mem := hf.x_mem, e₂_mem := hf.e₂_mem, e₃_mem := hf.e₃_mem, t_mem := ht', t_x := htx,
    t_e₂ := hte₂, t_e₃ := hte₃, ρ_mem := hρ', ρ_x := hρx, ρ_e₂ := hρe₂, ρ_e₃ := hρe₃,
    s_cases := hf.s_cases, lines := hf.lines }

end Frame

theorem exists_coreData {M O : Subgroup G} [hn : (O.subgroupOf M).Normal] {x e₂ e₃ t ρ : G}
    {s : ℤ} (hf : A6VIFrame M O x e₂ e₃ t ρ s) {Y U : Subgroup G} (hY2 : IsPGroup 2 Y)
    (hYM : Y ≤ M) (hYO : IsSylowOf 2 (Y ⊓ O) O) (hUQ : U ≤ Qf x e₂ e₃) (hU9 : Nat.card U = 9)
    (hxU : x ∈ U) (hUY : U ≤ normalizer (Y : Set G))
    (hedgeU : ∀ u ∈ U, (u ∈ zpowers x ∨ u ∈ zpowers e₂ ∨ u ∈ zpowers e₃) → u ∈ zpowers x)
    (hYN : ¬ Y ≤ normalizer ((Qf x e₂ e₃ ⊔ O : Subgroup G) : Set G))
    (hJ : ¬ ∃ E : Subgroup G, E ≤ normalizer ((thompsonJ Y : Subgroup G) : Set G) ⊓ M ∧
      IsElemAbelian 3 E ∧ Nat.card E = 27)
    (hodd : ∀ ℓ, (ℓ = x ∨ ℓ = e₂ ∨ ℓ = e₃) → ∀ w ∈ O, w ^ 2 = 1 → w * ℓ = ℓ * w → w = 1) :
    ∃ (t' ρ' : G) (Y' U' : Subgroup G) (x' : G), CoreData M O x e₂ e₃ t' ρ' s Y' U' x' := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hQ3 : IsPGroup 3 (Qf x e₂ e₃) :=
    IsPGroup.of_card (n := 3) (by rw [hf.Q_card]; norm_num)
  have hQO : Qf x e₂ e₃ ≤ normalizer (O : Set G) := hf.Q_le_N
  have hUR : U ≤ normalizer ((Y ⊓ O : Subgroup G) : Set G) := by
    intro u hu
    refine mem_normalizer_iff.mpr fun z => ?_
    have h1 := mem_normalizer_iff.mp (hUY hu) z
    have h2 := mem_normalizer_iff.mp (hf.O_norm (hf.Q_le_M (hUQ hu))) z
    rw [mem_inf, mem_inf, ← h1, ← h2]
  obtain ⟨c, hcQO, hQc, hUc⟩ :=
    GL83P3A6Syl.exists_conj_normalize hQ3 hf.O_cop hQO hYO hUQ hUR
  have hcM : c ∈ M := (sup_le hf.Q_le_M hf.O_le) hcQO
  have hcN : c ∈ normalizer (O : Set G) := hf.O_norm hcM
  set Y' : Subgroup G := Y.map (MulAut.conj c).toMonoidHom with hY'
  set U' : Subgroup G := U.map (MulAut.conj c).toMonoidHom with hU'
  have hR' : Y' ⊓ O = (Y ⊓ O).map (MulAut.conj c).toMonoidHom := by
    rw [Subgroup.map_inf _ _ (MulAut.conj c).toMonoidHom (MulAut.conj c).injective,
      GL83P3A6Syl.map_conj_eq hcN]
  have hYO' : IsSylowOf 2 (Y' ⊓ O) O := by
    rw [hR']
    exact GL83P3A6Syl.isSylowOf_conj hYO hcN
  have hQR' : Qf x e₂ e₃ ≤ normalizer ((Y' ⊓ O : Subgroup G) : Set G) := by
    rw [hR']
    exact hQc
  set E : Subgroup G := (Qf x e₂ e₃).map (MulAut.conj c⁻¹).toMonoidHom with hE
  have hER : E ≤ normalizer ((Y ⊓ O : Subgroup G) : Set G) := by
    rintro _ ⟨q, hq, rfl⟩
    refine mem_normalizer_iff.mpr fun z => ?_
    have h1 := mem_normalizer_iff.mp (hQc hq) (c * z * c⁻¹)
    rw [GL83P3A6Syl.mem_map_conj_iff, GL83P3A6Syl.mem_map_conj_iff] at h1
    have e1 : c⁻¹ * (c * z * c⁻¹) * c = z := by group
    have e2 : c⁻¹ * (q * (c * z * c⁻¹) * q⁻¹) * c = c⁻¹ * q * c * z * (c⁻¹ * q * c)⁻¹ := by
      group
    rw [e1, e2] at h1
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    exact h1
  have hEM : E ≤ M := by
    rintro _ ⟨q, hq, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    exact M.mul_mem (M.mul_mem (M.inv_mem hcM) (hf.Q_le_M hq)) hcM
  have hEel : IsElemAbelian 3 E := isElemAbelian_conj hf.Q_el c⁻¹
  have hE27 : Nat.card E = 27 := by
    rw [hE, Subgroup.card_map_of_injective (MulAut.conj c⁻¹).injective]
    exact hf.Q_card
  obtain ⟨A, hA, hAO⟩ := exists_offender hER hEM hEel hE27 hJ
  obtain ⟨ct, hctO, htR, htact⟩ := GL83P3A6Syl.exists_lift_normalizing hQ3 hf.O_cop hQO hYO'
    hQR' (hf.O_norm hf.t_mem) (t_mem_normalizer_Q hf)
  obtain ⟨cρ, hcρO, hρR, hρact⟩ := GL83P3A6Syl.exists_lift_normalizing hQ3 hf.O_cop hQO hYO'
    hQR' (hf.O_norm hf.ρ_mem) (ρ_mem_normalizer_Q hf)
  have hxQ : x ∈ Qf x e₂ e₃ := mem_sup_left (mem_zpowers x)
  have h2Q : e₂ ∈ Qf x e₂ e₃ := mem_sup_right (mem_sup_left (mem_zpowers e₂))
  have h3Q : e₃ ∈ Qf x e₂ e₃ := mem_sup_right (mem_sup_right (mem_zpowers e₃))
  have hf' : A6VIFrame M O x e₂ e₃ (ct * t) (cρ * ρ) s :=
    frame_replace hf (M.mul_mem (hf.O_le hctO.1) hf.t_mem)
      (by rw [htact x hxQ]; exact hf.t_x) (by rw [htact e₂ h2Q]; exact hf.t_e₂)
      (by rw [htact e₃ h3Q]; exact hf.t_e₃)
      (M.mul_mem (hf.O_le hcρO.1) hf.ρ_mem) (by rw [hρact x hxQ]; exact hf.ρ_x)
      (by rw [hρact e₂ h2Q]; exact hf.ρ_e₂) (by rw [hρact e₃ h3Q]; exact hf.ρ_e₃)
  have hx₁U : c * x * c⁻¹ ∈ U' := ⟨x, hxU, rfl⟩
  have hx₁Q : c * x * c⁻¹ ∈ Qf x e₂ e₃ := hUc hx₁U
  have hx₁3 : (c * x * c⁻¹) ^ 3 = 1 := by rw [conj_pow, hf.x_pow]; group
  have hx₁1 : c * x * c⁻¹ ≠ 1 := by
    intro h1
    apply hf.x_ne
    have : x = c⁻¹ * (c * x * c⁻¹) * c := by group
    rw [this, h1]; group
  obtain ⟨x', hx'ℓ, hx'zp⟩ : ∃ x', (x' = x ∨ x' = e₂ ∨ x' = e₃) ∧
      zpowers (c * x * c⁻¹) = zpowers x' := by
    rcases hf.lines c hx₁Q with h | h | h
    · exact ⟨x, Or.inl rfl, zpowers_eq_of_mem hf.x_pow hf.x_ne h hx₁1⟩
    · exact ⟨e₂, Or.inr (Or.inl rfl), zpowers_eq_of_mem hf.e₂_pow hf.e₂_ne h hx₁1⟩
    · exact ⟨e₃, Or.inr (Or.inr rfl), zpowers_eq_of_mem hf.e₃_pow hf.e₃_ne h hx₁1⟩
  have hx'U : x' ∈ U' := (zpowers_le.mpr hx₁U) (by rw [hx'zp]; exact mem_zpowers x')
  have hedge' : ∀ u ∈ U', (u ∈ zpowers x ∨ u ∈ zpowers e₂ ∨ u ∈ zpowers e₃) → u ∈ zpowers x' := by
    intro u hu hline
    by_cases hu1 : u = 1
    · rw [hu1]
      exact one_mem _
    obtain ⟨ℓ', hℓ', hmem⟩ : ∃ ℓ', (ℓ' = x ∨ ℓ' = e₂ ∨ ℓ' = e₃) ∧ u ∈ zpowers ℓ' := by
      rcases hline with h | h | h
      · exact ⟨x, Or.inl rfl, h⟩
      · exact ⟨e₂, Or.inr (Or.inl rfl), h⟩
      · exact ⟨e₃, Or.inr (Or.inr rfl), h⟩
    obtain ⟨hℓ3, hℓ1⟩ := gen_pow_three hf hℓ'
    have hzp : zpowers u = zpowers ℓ' := GL83P3A6Aux.zpowers_eq_of_mem hℓ3 hℓ1 hmem hu1
    have hℓ'U' : ℓ' ∈ U' := (zpowers_le.mpr hu) (by rw [hzp]; exact mem_zpowers ℓ')
    obtain ⟨u₀, hu₀U, hu₀⟩ := hℓ'U'
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hu₀
    have hu₀Q : u₀ ∈ Qf x e₂ e₃ := hUQ hu₀U
    have hconj : c⁻¹ * ℓ' * c⁻¹⁻¹ = u₀ := by rw [← hu₀]; group
    have hu₀line := conj_line hf hℓ' c⁻¹ (by rw [hconj]; exact hu₀Q)
    rw [hconj] at hu₀line
    have hu₀x : u₀ ∈ zpowers x := hedgeU u₀ hu₀U hu₀line
    have hℓ'x₁ : ℓ' ∈ zpowers (c * x * c⁻¹) := by
      obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hu₀x
      refine ⟨k, ?_⟩
      show (c * x * c⁻¹) ^ k = ℓ'
      rw [conj_zpow, hk]
      exact hu₀
    rw [hx'zp] at hℓ'x₁
    exact (zpowers_le.mpr hℓ'x₁) hmem
  refine ⟨ct * t, cρ * ρ, Y', U', x', ⟨hf', hY2.map _, ?_, hYO', htR, hρR, hQR', hUc, ?_, ?_,
    hx'ℓ, hx'U, hedge', ?_, ⟨A.map (MulAut.conj c).toMonoidHom, isMaxElemAbelian_conj hA c, ?_⟩,
    hodd⟩⟩
  · rintro _ ⟨y, hy, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact M.mul_mem (M.mul_mem hcM (hYM hy)) (M.inv_mem hcM)
  · rw [hU', Subgroup.card_map_of_injective (MulAut.conj c).injective]
    exact hU9
  · rintro _ ⟨u, hu, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    refine mem_normalizer_iff.mpr fun z => ?_
    rw [hY', GL83P3A6Syl.mem_map_conj_iff, GL83P3A6Syl.mem_map_conj_iff]
    have e : c⁻¹ * (c * u * c⁻¹ * z * (c * u * c⁻¹)⁻¹) * c = u * (c⁻¹ * z * c) * u⁻¹ := by group
    rw [e]
    exact mem_normalizer_iff.mp (hUY hu) _
  · intro hle
    apply hYN
    intro y hy
    have hc : c ∈ normalizer ((Qf x e₂ e₃ ⊔ O : Subgroup G) : Set G) := Subgroup.le_normalizer hcQO
    have h1 := hle ⟨y, hy, rfl⟩
    have e : y = c⁻¹ * (c * y * c⁻¹) * c := by group
    rw [e]
    exact (normalizer ((Qf x e₂ e₃ ⊔ O : Subgroup G) : Set G)).mul_mem
      ((normalizer ((Qf x e₂ e₃ ⊔ O : Subgroup G) : Set G)).mul_mem
        ((normalizer ((Qf x e₂ e₃ ⊔ O : Subgroup G) : Set G)).inv_mem hc) h1) hc
  · intro hle
    apply hAO
    intro a ha
    have h1 : c * a * c⁻¹ ∈ O := hle ⟨a, ha, rfl⟩
    have h2 := (mem_normalizer_iff.mp ((normalizer (O : Set G)).inv_mem hcN) (c * a * c⁻¹)).mp h1
    have e : c⁻¹ * (c * a * c⁻¹) * c⁻¹⁻¹ = a := by group
    rwa [e] at h2

end CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3A6Setup
