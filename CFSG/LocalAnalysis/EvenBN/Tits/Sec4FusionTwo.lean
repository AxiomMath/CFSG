module

public import CFSG.LocalAnalysis.EvenBN.Tits.Sec4Fusion
public import CFSG.GroupTheory.ABGLocalTools.Basic

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits

open Subgroup CFSG.Sporadic.Schreier.Tits

namespace Model

open CFSG.Quasithin (twoF4S)

theorem parrottV_five
    : parrottV 5 ∈ twoF4S ∧ parrottV 5 ∉ titsD ∧ parrottV 5 * parrottV 5 = titsZ := by
  refine ⟨parrottV_mem_twoF4S 5, fun h => ?_, by rw [parrott_squares.2.2.1, parrottV_twelve]⟩
  have h2 := (parrottV_mem_titsD_iff (i := 5) (by norm_num)).1 h
  exact h2 (by simp)

theorem conj_mem_titsD_iff {a x : Equiv.Perm (Fin 1755)}
    (ha : a ∈ titsA) (hx : x ∈ titsA) : a * x * a⁻¹ ∈ titsD ↔ x ∈ titsD := by
  rw [mul_mem_titsD_iff (mul_mem ha hx) (inv_mem ha), mul_mem_titsD_iff ha hx]
  have hinv : a⁻¹ ∈ titsD ↔ a ∈ titsD :=
    ⟨fun h => by simpa using inv_mem h, fun h => inv_mem h⟩
  rw [hinv]
  by_cases h1 : a ∈ titsD <;> by_cases h2 : x ∈ titsD <;>
    simp only [h1, h2, iff_self, iff_true, iff_false, not_true_eq_false]

end Model

namespace Data

variable {G : Type} [Group G] [Finite G] {d : Data G}

theorem Hyp.mul_self_ne_t
    (hd : d.Hyp) (y : G) : y * y ≠ d.t := by
  intro hyy
  have hy : y ∈ centralizer ({d.t} : Set G) := by
    rw [mem_centralizer_singleton_iff, ← hyy, mul_assoc]
  have h1 : (d.ρ ⟨y, hy⟩ : Equiv.Perm (Fin 1755)) * d.ρ ⟨y, hy⟩ = 1 := by
    have e : (⟨y, hy⟩ : centralizer ({d.t} : Set G)) * ⟨y, hy⟩ = ⟨d.t, d.t_mem_centralizer⟩ :=
      Subtype.ext hyy
    rw [← Subgroup.coe_mul, ← map_mul, e, hd.ρ_t, OneMemClass.coe_one]
  have hD : (d.ρ ⟨y, hy⟩ : Equiv.Perm (Fin 1755)) ∈ titsD := by
    by_cases h : (d.ρ ⟨y, hy⟩ : Equiv.Perm (Fin 1755)) = 1
    · rw [h]
      exact one_mem _
    · exact titsA_involution_mem_D (d.ρ ⟨y, hy⟩).2 (orderOf_eq_prime (by rw [sq]; exact h1) h)
  obtain ⟨l, hl⟩ : ∃ l, l = d.lift (d.ρ ⟨y, hy⟩ : Equiv.Perm (Fin 1755)) := ⟨_, rfl⟩
  have hlL : l ∈ d.L := hl ▸ d.lift_mem _
  have htl : d.t * l = l * d.t := (mem_centralizer_iff.1 hd.t_mem l hlL).symm
  have ht2 : d.t * d.t = 1 := by rw [← sq, ← hd.t_two, pow_orderOf_eq_one]
  apply hd.t_not_mem
  rw [← hyy]
  rcases hd.eq_lift_or hy hD with e | e
  · rw [← hl] at e
    rw [e]
    exact mul_mem hlL hlL
  · rw [← hl] at e
    have e2 : y * y = l * l := by
      rw [e]
      calc d.t * l * (d.t * l) = d.t * (l * d.t) * l := by group
        _ = d.t * d.t * (l * l) := by rw [← htl]; group
        _ = l * l := by rw [ht2, one_mul]
    rw [e2]
    exact mul_mem hlL hlL

theorem Hyp.mul_self_ne_conj_t
    (hd : d.Hyp) (y g : G) : y * y ≠ g * d.t * g⁻¹ := by
  intro h
  apply hd.mul_self_ne_t (g⁻¹ * y * g)
  calc g⁻¹ * y * g * (g⁻¹ * y * g) = g⁻¹ * (y * y) * g := by group
    _ = d.t := by rw [h]; group

theorem Hyp.t_mem_of_isSylowOf (hd : d.Hyp) {T : Subgroup G}
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T (centralizer ({d.t} : Set G))) : d.t ∈ T := by
  obtain ⟨Q, rfl⟩ := hT
  have : (zpowers (⟨d.t, d.t_mem_centralizer⟩ : centralizer ({d.t} : Set G))).Normal := by
    refine ⟨fun x hx g => ?_⟩
    have hc : g * x = x * g := by
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hx
      have : (⟨d.t, d.t_mem_centralizer⟩ : centralizer ({d.t} : Set G)) * g =
          g * ⟨d.t, d.t_mem_centralizer⟩ :=
        Subtype.ext (mem_centralizer_singleton_iff.1 g.2).symm
      exact ((Commute.zpow_left this k).eq).symm
    rw [hc, mul_inv_cancel_right]
    exact hx
  have hp : IsPGroup 2 (zpowers (⟨d.t, d.t_mem_centralizer⟩ : centralizer ({d.t} : Set G))) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, orderOf_mk, hd.t_two, pow_one])
  exact ⟨_, hp.le_sylow_of_normal Q (mem_zpowers _), rfl⟩

theorem Hyp.exists_complement
    (hd : d.Hyp) {T : Subgroup G}
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T (centralizer ({d.t} : Set G))) :
    ∃ Tt : Subgroup G, Tt ≤ T ∧ T ⊓ d.L ≤ Tt ∧ d.t ∉ Tt ∧ (∀ x ∈ T, x ∈ Tt ∨ d.t * x ∈ Tt) ∧
      Tt ⊓ centralizer (d.L : Set G) = ⊥ := by
  have htT := hd.t_mem_of_isSylowOf hT
  have hTC : T ≤ centralizer ({d.t} : Set G) := hT.le
  have ht2 : d.t * d.t = 1 := by rw [← sq, ← hd.t_two, pow_orderOf_eq_one]
  have hcL : ∀ l ∈ d.L, l * d.t = d.t * l := fun l hl => mem_centralizer_iff.1 hd.t_mem l hl
  have cover : ∀ x (hx : x ∈ centralizer ({d.t} : Set G)),
      (d.ρ ⟨x, hx⟩ : Equiv.Perm (Fin 1755)) ∈ titsD → x ∈ d.L ∨ d.t * x ∈ d.L := by
    intro x hx hD
    rcases hd.eq_lift_or hx hD with e | e
    · exact Or.inl (e ▸ d.lift_mem _)
    · refine Or.inr ?_
      rw [e, ← mul_assoc, ht2, one_mul]
      exact d.lift_mem _
  rcases hd.range_ρ with hR | hR
  ·
    refine ⟨T ⊓ d.L, inf_le_left, le_rfl, fun h => hd.t_not_mem h.2, fun x hx => ?_, ?_⟩
    · have hD : (d.ρ ⟨x, hTC hx⟩ : Equiv.Perm (Fin 1755)) ∈ titsD := by
        have h : d.ρ ⟨x, hTC hx⟩ ∈ d.ρ.range := ⟨_, rfl⟩
        rw [hR, mem_subgroupOf] at h
        exact h
      rcases cover x (hTC hx) hD with h | h
      · exact Or.inl ⟨hx, h⟩
      · exact Or.inr ⟨mul_mem htT hx, h⟩
    · rw [eq_bot_iff]
      rintro x ⟨⟨-, hxL⟩, hxC⟩
      have h : x ∈ d.L ⊓ centralizer (d.L : Set G) := ⟨hxL, hxC⟩
      rwa [hd.setting.inf_centralizer_eq_bot] at h
  ·
    obtain ⟨Q, rfl⟩ := hT
    have hsurj : Function.Surjective d.ρ := MonoidHom.range_eq_top.1 hR
    obtain ⟨P, hP⟩ := Model.exists_sylow_twoF4S
    obtain ⟨h5S, h5D, h5z⟩ := Model.parrottV_five
    set v5 := Model.parrottV 5 with hv5
    have h5A : v5 ∈ titsA :=
      (Model.twoF4S_le_twoF4H.trans Model.twoF4H_le_titsA) h5S
    obtain ⟨a, ha⟩ := MulAction.exists_smul_eq titsA P (Q.mapSurjective hsurj)
    have hmemP : (⟨v5, h5A⟩ : titsA) ∈ (P : Subgroup titsA) := by
      rw [hP]
      exact mem_subgroupOf.2 h5S
    have hmemQ : a * ⟨v5, h5A⟩ * a⁻¹ ∈ (Q.mapSurjective hsurj : Subgroup titsA) := by
      rw [← ha, Sylow.coe_subgroup_smul]
      exact Subgroup.smul_mem_pointwise_smul _ (MulAut.conj a) _ hmemP
    rw [Sylow.coe_mapSurjective, mem_map] at hmemQ
    obtain ⟨y', hy'Q, hy'⟩ := hmemQ
    obtain ⟨y, hyC⟩ := y'
    have hρy : (d.ρ ⟨y, hyC⟩ : Equiv.Perm (Fin 1755)) =
        (a : Equiv.Perm (Fin 1755)) * v5 * (a : Equiv.Perm (Fin 1755))⁻¹ := by
      rw [hy']
      rfl
    have hyT : y ∈ (Q : Subgroup (centralizer ({d.t} : Set G))).map
        (centralizer ({d.t} : Set G)).subtype := ⟨_, hy'Q, rfl⟩
    have hyD : (d.ρ ⟨y, hyC⟩ : Equiv.Perm (Fin 1755)) ∉ titsD := by
      rw [hρy, Model.conj_mem_titsD_iff a.2 h5A]
      exact h5D
    obtain ⟨δ, hδD, hδ⟩ := Model.exists_titsD_conj_titsZ a.2
    have hyy : y * y ∈ d.L := by
      have hyyC : y * y ∈ centralizer ({d.t} : Set G) := mul_mem hyC hyC
      have hρyy : (d.ρ ⟨y * y, hyyC⟩ : Equiv.Perm (Fin 1755)) = δ * titsZ * δ⁻¹ := by
        have e : (⟨y * y, hyyC⟩ : centralizer ({d.t} : Set G)) = ⟨y, hyC⟩ * ⟨y, hyC⟩ := rfl
        rw [e, map_mul, Subgroup.coe_mul, hρy, hδ]
        calc (a : Equiv.Perm (Fin 1755)) * v5 * (a : Equiv.Perm (Fin 1755))⁻¹ *
              ((a : Equiv.Perm (Fin 1755)) * v5 * (a : Equiv.Perm (Fin 1755))⁻¹) =
            (a : Equiv.Perm (Fin 1755)) * (v5 * v5) *
              (a : Equiv.Perm (Fin 1755))⁻¹ := by group
          _ = (a : Equiv.Perm (Fin 1755)) * titsZ * (a : Equiv.Perm (Fin 1755))⁻¹ := by rw [h5z]
      have hzD := titsZ_mem_titsD
      have hwD : δ * titsZ * δ⁻¹ ∈ titsD := mul_mem (mul_mem hδD hzD) (inv_mem hδD)
      have hw : d.lift (δ * titsZ * δ⁻¹) = d.lift δ * d.z * (d.lift δ)⁻¹ := by
        have hinv : d.lift δ⁻¹ = (d.lift δ)⁻¹ := by
          rw [← mul_eq_one_iff_eq_inv, ← d.lift_mul (inv_mem hδD) hδD, inv_mul_cancel,
            d.lift_one]
        rw [d.lift_mul (mul_mem hδD hzD) (inv_mem hδD), d.lift_mul hδD hzD, d.lift_titsZ, hinv]
      have hD : (d.ρ ⟨y * y, hyyC⟩ : Equiv.Perm (Fin 1755)) ∈ titsD := by
        rw [hρyy]
        exact hwD
      rcases hd.eq_lift_or hyyC hD with e | e
      · rw [e]
        exact d.lift_mem _
      · exfalso
        obtain ⟨g, hg⟩ := hd.exists_conj_eq_t_mul_z
        apply hd.mul_self_ne_conj_t y (d.lift δ * g)
        rw [e, hρyy, hw]
        have hδt : d.t * d.lift δ = d.lift δ * d.t := (hcL _ (d.lift_mem δ)).symm
        calc d.t * (d.lift δ * d.z * (d.lift δ)⁻¹) =
              d.t * d.lift δ * d.z * (d.lift δ)⁻¹ := by group
          _ = d.lift δ * (d.t * d.z) * (d.lift δ)⁻¹ := by rw [hδt]; group
          _ = d.lift δ * g * d.t * (d.lift δ * g)⁻¹ := by rw [← hg]; group
    set TG := (Q : Subgroup (centralizer ({d.t} : Set G))).map
      (centralizer ({d.t} : Set G)).subtype with hTG
    have hTGC : TG ≤ centralizer ({d.t} : Set G) := map_subtype_le _
    have hyN : ∀ l ∈ d.L, y⁻¹ * l * y ∈ d.L := fun l hl => by
      simpa using hd.conj_mem ⟨y, hyC⟩⁻¹ hl
    let Tt : Subgroup G :=
      { carrier := {x | x ∈ TG ∧ (x ∈ d.L ∨ y⁻¹ * x ∈ d.L)}
        mul_mem' := by
          rintro x₁ x₂ ⟨h1T, h1 | h1⟩ ⟨h2T, h2 | h2⟩
          · exact ⟨mul_mem h1T h2T, Or.inl (mul_mem h1 h2)⟩
          · refine ⟨mul_mem h1T h2T, Or.inr ?_⟩
            have e : y⁻¹ * (x₁ * x₂) = (y⁻¹ * x₁ * y) * (y⁻¹ * x₂) := by group
            rw [e]
            exact mul_mem (hyN x₁ h1) h2
          · refine ⟨mul_mem h1T h2T, Or.inr ?_⟩
            have e : y⁻¹ * (x₁ * x₂) = (y⁻¹ * x₁) * x₂ := by group
            rw [e]
            exact mul_mem h1 h2
          · refine ⟨mul_mem h1T h2T, Or.inl ?_⟩
            have e : x₁ * x₂ = (y * y) * (y⁻¹ * (y⁻¹ * x₁) * y) * (y⁻¹ * x₂) := by group
            rw [e]
            exact mul_mem (mul_mem hyy (hyN _ h1)) h2
        one_mem' := ⟨one_mem _, Or.inl (one_mem _)⟩
        inv_mem' := by
          rintro x ⟨hxT, hx | hx⟩
          · exact ⟨inv_mem hxT, Or.inl (inv_mem hx)⟩
          · refine ⟨inv_mem hxT, Or.inr ?_⟩
            have e : y⁻¹ * x⁻¹ = y⁻¹ * (y⁻¹ * x)⁻¹ * y * (y * y)⁻¹ := by group
            rw [e]
            exact mul_mem (hyN _ (inv_mem hx)) (inv_mem hyy) }
    have hmemTt : ∀ x, x ∈ Tt ↔ x ∈ TG ∧ (x ∈ d.L ∨ y⁻¹ * x ∈ d.L) := fun x => Iff.rfl
    have htTt : d.t ∉ Tt := by
      rintro ⟨-, h | h⟩
      · exact hd.t_not_mem h
      ·
        apply hyD
        have hl : y⁻¹ * d.t ∈ centralizer ({d.t} : Set G) :=
          mul_mem (inv_mem hyC) d.t_mem_centralizer
        have e1 : (d.ρ ⟨y⁻¹ * d.t, hl⟩ : Equiv.Perm (Fin 1755)) ∈ titsD := by
          rw [hd.ρ_eq_θ ⟨_, h⟩]
          exact (d.θ _).2
        have e2 : (⟨y⁻¹ * d.t, hl⟩ : centralizer ({d.t} : Set G)) =
            (⟨y, hyC⟩)⁻¹ * ⟨d.t, d.t_mem_centralizer⟩ := rfl
        rw [e2, map_mul, map_inv, hd.ρ_t, mul_one, Subgroup.coe_inv] at e1
        simpa using inv_mem e1
    refine ⟨Tt, fun x hx => hx.1, fun x hx => ⟨hx.1, Or.inl hx.2⟩, htTt, fun x hx => ?_, ?_⟩
    · have hxC := hTGC hx
      by_cases hxD : (d.ρ ⟨x, hxC⟩ : Equiv.Perm (Fin 1755)) ∈ titsD
      · rcases cover x hxC hxD with h | h
        · exact Or.inl ⟨hx, Or.inl h⟩
        · exact Or.inr ⟨mul_mem htT hx, Or.inl h⟩
      ·
        have hyx : y⁻¹ * x ∈ centralizer ({d.t} : Set G) := mul_mem (inv_mem hyC) hxC
        have hD : (d.ρ ⟨y⁻¹ * x, hyx⟩ : Equiv.Perm (Fin 1755)) ∈ titsD := by
          have e : (⟨y⁻¹ * x, hyx⟩ : centralizer ({d.t} : Set G)) = (⟨y, hyC⟩)⁻¹ * ⟨x, hxC⟩ :=
            rfl
          rw [e, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]
          exact (Model.mul_mem_titsD_iff (inv_mem (d.ρ ⟨y, hyC⟩).2) (d.ρ ⟨x, hxC⟩).2).2
            (iff_of_false (fun h => hyD (by simpa using inv_mem h)) hxD)
        rcases cover _ hyx hD with h | h
        · exact Or.inl ⟨hx, Or.inr h⟩
        · refine Or.inr ⟨mul_mem htT hx, Or.inr ?_⟩
          have hyt : y⁻¹ * d.t = d.t * y⁻¹ := by
            have := mem_centralizer_singleton_iff.1 (inv_mem hyC)
            exact this
          rw [← mul_assoc, hyt, mul_assoc]
          exact h
    · rw [eq_bot_iff]
      rintro x ⟨hxTt, hxL⟩
      have hk : x ∈ centralizer (d.L : Set G) ⊓ centralizer ({d.t} : Set G) :=
        ⟨hxL, hTGC hxTt.1⟩
      rw [Model.kernel_eq_zpowers_of_hyp hd, Model.mem_zpowers_of_orderOf_two hd.t_two] at hk
      rcases hk with h | h
      · exact h
      · exact absurd (h ▸ hxTt) htTt

theorem Hyp.card_le_of_isElemAbelian
    (hd : d.Hyp) {E : Subgroup G} (hE : E ≤ centralizer ({d.t} : Set G))
    (hEa : CFSG.Open.IsElemAbelian 2 E) : Nat.card E ≤ 2 ^ 6 := by
  obtain ⟨hcomm, h2⟩ := hEa
  have hcE : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hcomm.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hsq : ∀ x ∈ E, x * x = 1 := fun x hx => by rw [← sq]; exact h2 x hx
  have ht2 : d.t * d.t = 1 := by rw [← sq, ← hd.t_two, pow_orderOf_eq_one]
  have hcL : ∀ l ∈ d.L, l * d.t = d.t * l := fun l hl => mem_centralizer_iff.1 hd.t_mem l hl
  have htt : ∀ a ∈ d.L, ∀ b : G, d.t * a * (d.t * b) = a * b := fun a ha b => by
    calc d.t * a * (d.t * b) = d.t * (a * d.t) * b := by group
      _ = d.t * (d.t * a) * b := by rw [hcL a ha]
      _ = a * b := by rw [← mul_assoc, ht2, one_mul]
  let P : Subgroup G :=
    { carrier := {l | l ∈ d.L ∧ (l ∈ E ∨ d.t * l ∈ E)}
      mul_mem' := by
        rintro a b ⟨haL, ha | ha⟩ ⟨hbL, hb | hb⟩
        · exact ⟨mul_mem haL hbL, Or.inl (mul_mem ha hb)⟩
        · refine ⟨mul_mem haL hbL, Or.inr ?_⟩
          have e : d.t * (a * b) = a * (d.t * b) := by
            rw [← mul_assoc, ← hcL a haL, mul_assoc]
          rw [e]
          exact mul_mem ha hb
        · refine ⟨mul_mem haL hbL, Or.inr ?_⟩
          rw [← mul_assoc]
          exact mul_mem ha hb
        · refine ⟨mul_mem haL hbL, Or.inl ?_⟩
          rw [← htt a haL b]
          exact mul_mem ha hb
      one_mem' := ⟨one_mem _, Or.inl (one_mem _)⟩
      inv_mem' := by
        rintro a ⟨haL, ha | ha⟩
        · exact ⟨inv_mem haL, Or.inl (inv_mem ha)⟩
        · refine ⟨inv_mem haL, Or.inr ?_⟩
          have e : d.t * a⁻¹ = (d.t * a)⁻¹ := by
            rw [mul_inv_rev, inv_eq_of_mul_eq_one_right ht2]
            exact (hcL _ (inv_mem haL)).symm
          rw [e]
          exact inv_mem ha }
  have hPL : P ≤ d.L := fun l hl => hl.1
  have hPc : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a := by
    rintro a ⟨haL, ha | ha⟩ b ⟨hbL, hb | hb⟩
    · exact hcE a ha b hb
    · have h := hcE a ha _ hb
      rw [← mul_assoc, hcL a haL, mul_assoc, mul_assoc] at h
      exact mul_left_cancel h
    · have h := hcE _ ha b hb
      rw [mul_assoc, ← mul_assoc b, hcL b hbL, mul_assoc] at h
      exact mul_left_cancel h
    · have h := hcE _ ha _ hb
      rwa [htt a haL b, htt b hbL a] at h
  have hPsq : ∀ a ∈ P, a * a = 1 := by
    rintro a ⟨haL, ha | ha⟩
    · exact hsq a ha
    · rw [← htt a haL a]
      exact hsq _ ha
  have hX := Model.card_le_of_elemAbelian_titsA
    (X := ((P.subgroupOf d.L).map d.θ.toMonoidHom).map titsD.subtype)
    ((map_subtype_le _).trans titsD_le_titsA) (by
      rintro _ ⟨_, ⟨a, ha, rfl⟩, rfl⟩ _ ⟨_, ⟨b, hb, rfl⟩, rfl⟩
      have hab : a * b = b * a := Subtype.ext (hPc _ (mem_subgroupOf.1 ha) _ (mem_subgroupOf.1 hb))
      simp only [MulEquiv.coe_toMonoidHom, coe_subtype]
      rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul, hab]) (by
      rintro _ ⟨_, ⟨a, ha, rfl⟩, rfl⟩
      have haa : a * a = 1 := Subtype.ext (hPsq _ (mem_subgroupOf.1 ha))
      simp only [MulEquiv.coe_toMonoidHom, coe_subtype]
      rw [← Subgroup.coe_mul, ← map_mul, haa, map_one, OneMemClass.coe_one])
  have hcardX : Nat.card (((P.subgroupOf d.L).map d.θ.toMonoidHom).map titsD.subtype) =
      Nat.card P := by
    rw [card_map_of_injective titsD.subtype_injective,
      card_map_of_injective (f := d.θ.toMonoidHom) d.θ.injective,
      Nat.card_congr (subgroupOfEquivOfLe hPL).toEquiv]
  have hsub : (E : Set G) ⊆ (P : Set G) ∪ (fun x => d.t * x) '' (P : Set G) := by
    intro x hx
    rcases hd.involution_mem (hE hx) (h2 x hx) with h | h
    · exact Or.inl ⟨h, Or.inl hx⟩
    · refine Or.inr ⟨d.t * x, ⟨h, Or.inr ?_⟩, ?_⟩
      · rw [← mul_assoc, ht2, one_mul]
        exact hx
      · show d.t * (d.t * x) = x
        rw [← mul_assoc, ht2, one_mul]
  calc Nat.card E = (E : Set G).ncard := Nat.card_coe_set_eq _
    _ ≤ ((P : Set G) ∪ (fun x => d.t * x) '' (P : Set G)).ncard :=
        Set.ncard_le_ncard hsub (Set.toFinite _)
    _ ≤ (P : Set G).ncard + ((fun x => d.t * x) '' (P : Set G)).ncard := Set.ncard_union_le _ _
    _ = 2 * Nat.card P := by
        rw [Set.ncard_image_of_injective _ (mul_right_injective d.t), two_mul,
          ← Nat.card_coe_set_eq]
        rfl
    _ ≤ 2 ^ 6 := by
        rw [← hcardX]
        have := hX.2
        omega

end Data

end CFSG.LocalAnalysis.EvenBN.Tits
