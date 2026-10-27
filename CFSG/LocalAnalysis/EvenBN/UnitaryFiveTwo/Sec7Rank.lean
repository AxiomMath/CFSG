module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.ModelCheckAut
public import CFSG.GroupTheory.CommutingProductFixedSubgroup

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup

theorem sup_comm_of {X : Type*} [Group X] {H K : Subgroup X}
    (hH : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a) (hK : ∀ a ∈ K, ∀ b ∈ K, a * b = b * a)
    (hHK : ∀ a ∈ H, ∀ b ∈ K, a * b = b * a) :
    ∀ x ∈ H ⊔ K, ∀ y ∈ H ⊔ K, x * y = y * x := by
  have hCH : ∀ h ∈ H, H ⊔ K ≤ centralizer ({h} : Set X) := fun h hh =>
    sup_le (fun h' hh' => mem_centralizer_singleton_iff.2 (hH h' hh' h hh))
      (fun k hk => mem_centralizer_singleton_iff.2 (hHK h hh k hk).symm)
  have hCK : ∀ k ∈ K, H ⊔ K ≤ centralizer ({k} : Set X) := fun k hk =>
    sup_le (fun h' hh' => mem_centralizer_singleton_iff.2 (hHK h' hh' k hk))
      (fun k' hk' => mem_centralizer_singleton_iff.2 (hK k' hk' k hk))
  have hT : H ⊔ K ≤ centralizer ((H ⊔ K : Subgroup X) : Set X) :=
    sup_le (fun h hh => mem_centralizer_iff.2 fun g hg =>
      mem_centralizer_singleton_iff.1 (hCH h hh hg))
      (fun k hk => mem_centralizer_iff.2 fun g hg =>
        mem_centralizer_singleton_iff.1 (hCK k hk hg))
  intro x hx y hy
  exact mem_centralizer_iff.1 (hT hy) x hx

theorem fld_fix_ZX₁sub : ∀ g ∈ ZX₁sub, fld g = g := by
  intro g hg
  obtain ⟨a, b, ha, hg⟩ := mem_x₁Sub.1 hg
  subst ha
  have hb : bar b = b := by
    rcases eq_zero_or_one_of_valid b (x₁_coord_rel hg) with rfl | rfl
    · exact map_zero _
    · exact map_one _
  exact ext_mat (by rw [mat_fld, hg, x₁Mat_map_bar, map_zero, hb])

theorem fld_fix_ZX₄sub : ∀ g ∈ ZX₄sub, fld g = g := by
  intro g hg
  obtain ⟨a, b, ha, hg⟩ := mem_x₄Sub.1 hg
  subst ha
  have hb : bar b = b := by
    rcases eq_zero_or_one_of_valid b (x₄_coord_rel hg) with rfl | rfl
    · exact map_zero _
    · exact map_one _
  exact ext_mat (by rw [mat_fld, hg, x₄Mat_map_bar, map_zero, hb])

theorem X₃zsub_le_X₃sub : X₃zsub ≤ X₃sub := fun g hg => by
  obtain ⟨a, -, hg⟩ := mem_x₃Sub.1 hg
  exact mem_X₃sub.2 ⟨a, hg⟩

theorem fld_fix_X₃zsub : ∀ g ∈ X₃zsub, fld g = g := by
  intro g hg
  obtain ⟨a, ha, hg⟩ := mem_x₃Sub.1 hg
  exact ext_mat (by rw [mat_fld, hg, x₃Mat_map_bar, ha])

theorem ZX₁sub_le_Fsub : ZX₁sub ≤ Fsub := fun g hg => mem_sup_left (mem_sup_left hg)

theorem X₃zsub_le_Fsub : X₃zsub ≤ Fsub :=
  fun g hg => mem_sup_left (mem_sup_right (X₃zsub_le_X₃sub hg))

theorem ZX₄sub_le_Fsub : ZX₄sub ≤ Fsub := fun g hg => mem_sup_right hg

theorem exists_elemAb_fixed_fld :
    ∃ E : Subgroup SU52, (∀ x ∈ E, x * x = 1) ∧ (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) ∧
      8 ≤ Nat.card E ∧ ∀ x ∈ E, fld x = x := by
  have hle1 : ZX₁sub ⊔ X₃zsub ≤ Fsub := sup_le ZX₁sub_le_Fsub X₃zsub_le_Fsub
  have hle : ZX₁sub ⊔ X₃zsub ⊔ ZX₄sub ≤ Fsub := sup_le hle1 ZX₄sub_le_Fsub
  have hfix : ZX₁sub ⊔ X₃zsub ⊔ ZX₄sub ≤ CfldSub :=
    sup_le (sup_le (fun g hg => mem_CfldSub.2 (fld_fix_ZX₁sub g hg))
      (fun g hg => mem_CfldSub.2 (fld_fix_X₃zsub g hg)))
      (fun g hg => mem_CfldSub.2 (fld_fix_ZX₄sub g hg))
  have hmem : ∀ y₁ ∈ ZX₁sub, ∀ y₂ ∈ (⊥ : Subgroup SU52), ∀ y₃ ∈ X₃zsub, ∀ y₄ ∈ ZX₄sub,
      y₁ * y₂ * y₃ * y₄ ∈ ZX₁sub ⊔ X₃zsub ⊔ ZX₄sub := by
    intro y₁ hy₁ y₂ hy₂ y₃ hy₃ y₄ hy₄
    rw [Subgroup.mem_bot.1 hy₂, mul_one]
    exact mul_mem (mul_mem (mem_sup_left (mem_sup_left hy₁))
      (mem_sup_left (mem_sup_right hy₃))) (mem_sup_right hy₄)
  have hsurj : ∀ g ∈ ZX₁sub ⊔ X₃zsub ⊔ ZX₄sub, ∃ y₁ ∈ ZX₁sub, ∃ y₂ ∈ (⊥ : Subgroup SU52),
      ∃ y₃ ∈ X₃zsub, ∃ y₄ ∈ ZX₄sub, g = y₁ * y₂ * y₃ * y₄ := by
    intro g hg
    obtain ⟨a, ha, b, hb, rfl⟩ := CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute
      (A := ZX₁sub ⊔ X₃zsub) (B := ZX₄sub)
      (fun a ha b hb => Fsub_comm (hle1 ha) (ZX₄sub_le_Fsub hb)) hg
    obtain ⟨c, hc, d, hd, rfl⟩ := CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute
      (A := ZX₁sub) (B := X₃zsub)
      (fun c hc d hd => Fsub_comm (ZX₁sub_le_Fsub hc) (X₃zsub_le_Fsub hd)) ha
    exact ⟨c, hc, 1, Subgroup.one_mem _, d, hd, b, hb, by group⟩
  have hcard : Nat.card (ZX₁sub ⊔ X₃zsub ⊔ ZX₄sub : Subgroup SU52) = 8 := by
    have h := card_of_nf (H := ZX₁sub ⊔ X₃zsub ⊔ ZX₄sub) (Y₁ := ZX₁sub) (Y₂ := ⊥)
      (Y₃ := X₃zsub) (Y₄ := ZX₄sub) ZX₁sub_le_X₁sub bot_le X₃zsub_le_X₃sub ZX₄sub_le_X₄sub
      hmem hsurj
    rw [card_ZX₁sub, Subgroup.card_bot, card_X₃zsub, card_ZX₄sub] at h
    norm_num at h
    exact h
  refine ⟨ZX₁sub ⊔ X₃zsub ⊔ ZX₄sub, fun x hx => Fsub_sq (hle hx),
    fun x hx y hy => Fsub_comm (hle hx) (hle hy), le_of_eq hcard.symm,
    fun x hx => mem_CfldSub.1 (hfix hx)⟩

theorem Fsub_le_Ssub : Fsub ≤ Ssub := fun g hg => (mem_Fsub.1 hg).1

theorem conj_Fsub_eq {s : SU52} (hsS : s ∈ Ssub) :
    Fsub.map (MulAut.conj s).toMonoidHom = Fsub := by
  refine eq_Fsub_of_elemAb_Ssub ?_ ?_ ?_ ?_
  · rintro _ ⟨x, hx, rfl⟩
    exact mul_mem (mul_mem hsS (Fsub_le_Ssub hx)) (inv_mem hsS)
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    change MulAut.conj s x * MulAut.conj s y = MulAut.conj s y * MulAut.conj s x
    rw [← map_mul, ← map_mul, Fsub_comm hx hy]
  · rintro _ ⟨x, hx, rfl⟩
    change MulAut.conj s x * MulAut.conj s x = 1
    rw [← map_mul, Fsub_sq hx, map_one]
  · rw [Subgroup.card_map_of_injective (MulAut.conj s).injective, card_Fsub]
    norm_num

theorem elemAb_centralizer_ssub {s : SU52} (hss : s * s = 1) (hsS : s ∈ Ssub) :
    ∃ E : Subgroup SU52, (∀ x ∈ E, x * x = 1) ∧ (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) ∧
      8 ≤ Nat.card E ∧ ∀ x ∈ E, s * x = x * s := by
  by_cases hF : s ∈ Fsub
  · refine ⟨Fsub, fun x hx => Fsub_sq hx, fun x hx y hy => Fsub_comm hx hy, ?_,
      fun x hx => Fsub_comm hF hx⟩
    rw [card_Fsub]
    norm_num
  have hnorm : ∀ v ∈ Fsub, s * v * s⁻¹ ∈ Fsub := by
    intro v hv
    have hmem : MulAut.conj s v ∈ Fsub.map (MulAut.conj s).toMonoidHom := ⟨v, hv, rfl⟩
    rw [conj_Fsub_eq hsS] at hmem
    exact hmem
  obtain ⟨ψ, hψ⟩ : ∃ ψ : Fsub →* Fsub,
      ∀ v : Fsub, (ψ v : SU52) = s * (v : SU52) * s⁻¹ * (v : SU52)⁻¹ := by
    refine ⟨MonoidHom.mk' (fun v => ⟨s * (v : SU52) * s⁻¹ * (v : SU52)⁻¹,
      mul_mem (hnorm v v.2) (inv_mem v.2)⟩) ?_, fun v => rfl⟩
    intro v w
    apply Subtype.ext
    show s * ((v : SU52) * (w : SU52)) * s⁻¹ * ((v : SU52) * (w : SU52))⁻¹ =
      (s * (v : SU52) * s⁻¹ * (v : SU52)⁻¹) * (s * (w : SU52) * s⁻¹ * (w : SU52)⁻¹)
    have hWw : (s * (w : SU52) * s⁻¹ * (w : SU52)⁻¹) * (v : SU52)⁻¹ =
        (v : SU52)⁻¹ * (s * (w : SU52) * s⁻¹ * (w : SU52)⁻¹) :=
      Fsub_comm (mul_mem (hnorm w w.2) (inv_mem w.2)) (inv_mem v.2)
    calc s * ((v : SU52) * (w : SU52)) * s⁻¹ * ((v : SU52) * (w : SU52))⁻¹
        = (s * (v : SU52) * s⁻¹) * ((s * (w : SU52) * s⁻¹ * (w : SU52)⁻¹) * (v : SU52)⁻¹) := by
          group
      _ = (s * (v : SU52) * s⁻¹) * ((v : SU52)⁻¹ * (s * (w : SU52) * s⁻¹ * (w : SU52)⁻¹)) := by
          rw [hWw]
      _ = _ := by group
  have hker : ∀ v : Fsub, ψ v = 1 ↔ s * (v : SU52) * s⁻¹ = v := by
    intro v
    constructor
    · intro h
      have h1 : (ψ v : SU52) = 1 := congrArg Subtype.val h
      rw [hψ] at h1
      exact mul_inv_eq_one.1 h1
    · intro h
      apply Subtype.ext
      show (ψ v : SU52) = 1
      rw [hψ, h, mul_inv_cancel]
  have hrange : ψ.range ≤ ψ.ker := by
    rintro _ ⟨v, rfl⟩
    rw [MonoidHom.mem_ker, hker]
    have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hss
    have hsq : (ψ v : SU52) * (ψ v : SU52) = 1 := Fsub_sq (ψ v).2
    have hu' : (ψ v : SU52)⁻¹ = (ψ v : SU52) := inv_eq_of_mul_eq_one_right hsq
    calc s * (ψ v : SU52) * s⁻¹ = (s * s) * ((v : SU52) * s⁻¹ * (v : SU52)⁻¹ * s⁻¹) := by
          rw [hψ]
          group
      _ = (v : SU52) * s⁻¹ * (v : SU52)⁻¹ * s⁻¹ := by rw [hss, one_mul]
      _ = (v : SU52) * s * (v : SU52)⁻¹ * s⁻¹ := by rw [hsinv]
      _ = (ψ v : SU52)⁻¹ := by rw [hψ]; group
      _ = (ψ v : SU52) := hu'
  have hcardeq : Nat.card ψ.ker * Nat.card ψ.range = 16 := by
    have h := Subgroup.card_mul_index ψ.ker
    rw [Subgroup.index_ker, card_Fsub] at h
    exact h
  have hle : Nat.card ψ.range ≤ Nat.card ψ.ker := Subgroup.card_le_of_le hrange
  have hk4 : 4 ≤ Nat.card ψ.ker := by
    by_contra hlt
    have h3 : Nat.card ψ.ker ≤ 3 := by omega
    have hmul : Nat.card ψ.ker * Nat.card ψ.range ≤ Nat.card ψ.ker * Nat.card ψ.ker :=
      Nat.mul_le_mul_left _ hle
    have hsq9 : Nat.card ψ.ker * Nat.card ψ.ker ≤ 3 * 3 := Nat.mul_le_mul h3 h3
    have h16 : 16 ≤ 3 * 3 := by
      rw [← hcardeq]
      exact hmul.trans hsq9
    omega
  obtain ⟨E₀, hE₀⟩ : ∃ E₀ : Subgroup SU52, E₀ = ψ.ker.map Fsub.subtype := ⟨_, rfl⟩
  have hE₀card : Nat.card E₀ = Nat.card ψ.ker := by
    rw [hE₀]
    exact Subgroup.card_map_of_injective Fsub.subtype_injective
  have hE₀mem : ∀ x ∈ E₀, x ∈ Fsub ∧ s * x = x * s := by
    intro x hx
    rw [hE₀] at hx
    obtain ⟨v, hv, rfl⟩ := hx
    have hv' : s * (v : SU52) * s⁻¹ = v := (hker v).1 (MonoidHom.mem_ker.1 hv)
    refine ⟨v.2, ?_⟩
    calc s * (v : SU52) = s * (v : SU52) * s⁻¹ * s := by group
      _ = (v : SU52) * s := by rw [hv']
  have hE₀F : ∀ x ∈ E₀, x ∈ Fsub := fun x hx => (hE₀mem x hx).1
  have hcomm_zpowers : ∀ a ∈ zpowers s, ∀ b ∈ zpowers s, a * b = b * a := by
    intro a ha b hb
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 ha
    obtain ⟨m, rfl⟩ := mem_zpowers_iff.1 hb
    exact zpow_mul_comm s k m
  have hcomm_E₀ : ∀ a ∈ E₀, ∀ b ∈ E₀, a * b = b * a := fun a ha b hb =>
    Fsub_comm (hE₀F a ha) (hE₀F b hb)
  have hcommHK : ∀ a ∈ zpowers s, ∀ b ∈ E₀, a * b = b * a := by
    intro a ha b hb
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 ha
    exact ((show Commute s b from (hE₀mem b hb).2).zpow_left k).eq
  have hsq : ∀ x ∈ zpowers s ⊔ E₀, x * x = 1 := by
    intro x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute hcommHK hx
    have haa : a * a = 1 := by
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 ha
      rw [← zpow_add, ← two_mul, zpow_mul, zpow_two, hss, one_zpow]
    have hbb : b * b = 1 := Fsub_sq (hE₀F b hb)
    calc a * b * (a * b) = a * (b * a) * b := by group
      _ = a * (a * b) * b := by rw [(hcommHK a ha b hb).symm]
      _ = (a * a) * (b * b) := by group
      _ = 1 := by rw [haa, hbb, one_mul]
  have hcentr : ∀ x ∈ zpowers s ⊔ E₀, s * x = x * s := by
    have hsub : zpowers s ⊔ E₀ ≤ centralizer ({s} : Set SU52) :=
      sup_le (zpowers_le.2 (mem_centralizer_singleton_iff.2 rfl))
        (fun b hb => mem_centralizer_singleton_iff.2 (hE₀mem b hb).2.symm)
    intro x hx
    exact (mem_centralizer_singleton_iff.1 (hsub hx)).symm
  have hmemE : ∀ (b : Bool) (c : E₀), (if b then s else 1) * (c : SU52) ∈ zpowers s ⊔ E₀ := by
    intro b c
    refine mul_mem ?_ (mem_sup_right c.2)
    cases b
    · exact one_mem _
    · exact mem_sup_left (mem_zpowers s)
  have hinj : Function.Injective (fun p : Bool × E₀ =>
      (⟨(if p.1 then s else 1) * (p.2 : SU52), hmemE p.1 p.2⟩ : ↥(zpowers s ⊔ E₀))) := by
    rintro ⟨b, c⟩ ⟨b', c'⟩ h
    have h' : (if b then s else 1) * (c : SU52) = (if b' then s else 1) * (c' : SU52) :=
      congrArg Subtype.val h
    cases b <;> cases b'
    · have hc : (c : SU52) = c' := by simpa using h'
      rw [Subtype.ext hc]
    · exfalso
      have h2 : s * (c' : SU52) = (c : SU52) := by simpa using h'.symm
      have hs : s ∈ Fsub := by
        rw [show s = (c : SU52) * (c' : SU52)⁻¹ from eq_mul_inv_of_mul_eq h2]
        exact mul_mem (hE₀F c c.2) (inv_mem (hE₀F c' c'.2))
      exact hF hs
    · exfalso
      have h2 : s * (c : SU52) = (c' : SU52) := by simpa using h'
      have hs : s ∈ Fsub := by
        rw [show s = (c' : SU52) * (c : SU52)⁻¹ from eq_mul_inv_of_mul_eq h2]
        exact mul_mem (hE₀F c' c'.2) (inv_mem (hE₀F c c.2))
      exact hF hs
    · have hc : (c : SU52) = c' := by
        have h2 : s * (c : SU52) = s * (c' : SU52) := by simpa using h'
        exact mul_left_cancel h2
      rw [Subtype.ext hc]
  have h2B : Nat.card Bool = 2 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_bool]
  have hcard2 : Nat.card (Bool × E₀) ≤ Nat.card ↥(zpowers s ⊔ E₀) :=
    Nat.card_le_card_of_injective _ hinj
  rw [Nat.card_prod, h2B, hE₀card] at hcard2
  refine ⟨zpowers s ⊔ E₀, hsq, sup_comm_of hcomm_zpowers hcomm_E₀ hcommHK, ?_, hcentr⟩
  omega

theorem exists_elemAb_centralizer_involution (s : SU52) (hs : s * s = 1) :
    ∃ E : Subgroup SU52, (∀ x ∈ E, x * x = 1) ∧ (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) ∧
      8 ≤ Nat.card E ∧ ∀ x ∈ E, s * x = x * s := by
  have hzs : IsPGroup 2 (zpowers s) := isPGroup_two_of_sq fun y hy => by
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hy
    rw [← zpow_add, ← two_mul, zpow_mul, zpow_two, hs, one_zpow]
  obtain ⟨g, hg⟩ := exists_conj_le_Ssub hzs
  have hsS : g * s * g⁻¹ ∈ Ssub := hg ⟨s, mem_zpowers s, rfl⟩
  have hs' : (g * s * g⁻¹) * (g * s * g⁻¹) = 1 := by
    calc (g * s * g⁻¹) * (g * s * g⁻¹) = g * (s * s) * g⁻¹ := by group
      _ = 1 := by rw [hs]; group
  obtain ⟨E', h1, h2, h3, h4⟩ := elemAb_centralizer_ssub hs' hsS
  refine ⟨E'.map (MulAut.conj g⁻¹).toMonoidHom, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    change MulAut.conj g⁻¹ y * MulAut.conj g⁻¹ y = 1
    rw [← map_mul, h1 y hy, map_one]
  · rintro _ ⟨y, hy, rfl⟩ _ ⟨z, hz, rfl⟩
    change MulAut.conj g⁻¹ y * MulAut.conj g⁻¹ z = MulAut.conj g⁻¹ z * MulAut.conj g⁻¹ y
    rw [← map_mul, ← map_mul, h2 y hy z hz]
  · rw [Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective]
    exact h3
  · rintro _ ⟨y, hy, rfl⟩
    change s * (g⁻¹ * y * g⁻¹⁻¹) = (g⁻¹ * y * g⁻¹⁻¹) * s
    rw [inv_inv]
    calc s * (g⁻¹ * y * g) = g⁻¹ * ((g * s * g⁻¹) * y) * g := by group
      _ = g⁻¹ * (y * (g * s * g⁻¹)) * g := by rw [h4 y hy]
      _ = (g⁻¹ * y * g) * s := by group

theorem exists_elemAb_fixed (θ : MulAut SU52)
    (hθ : θ * θ = 1) :
    ∃ E : Subgroup SU52, (∀ x ∈ E, x * x = 1) ∧ (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) ∧
      8 ≤ Nat.card E ∧ ∀ x ∈ E, θ x = x := by
  obtain ⟨s, rfl | rfl⟩ := exists_eq_conj_or_eq_conj_mul_fld θ
  ·
    have hss : s * s = 1 := by
      rw [← map_mul] at hθ
      exact (conj_eq_one_iff (s * s)).1 hθ
    obtain ⟨E, h1, h2, h3, h4⟩ := exists_elemAb_centralizer_involution s hss
    refine ⟨E, h1, h2, h3, fun x hx => ?_⟩
    change s * x * s⁻¹ = x
    rw [h4 x hx, mul_inv_cancel_right]
  ·
    have hxo : fieldFactor (MulAut.conj s * fld) ≠ 1 := fieldFactor_conj_mul_fld s
    obtain ⟨n, hn⟩ := exists_conj_eq_fld hxo hθ
    obtain ⟨E, h1, h2, h3, h4⟩ := exists_elemAb_fixed_fld
    have hθ' : MulAut.conj s * fld = MulAut.conj n⁻¹ * fld * MulAut.conj n := by
      calc MulAut.conj s * fld
          = (MulAut.conj n)⁻¹ * (MulAut.conj n * (MulAut.conj s * fld) * (MulAut.conj n)⁻¹) *
            MulAut.conj n := by group
        _ = (MulAut.conj n)⁻¹ * fld * MulAut.conj n := by rw [hn]
        _ = MulAut.conj n⁻¹ * fld * MulAut.conj n := by rw [map_inv]
    refine ⟨E.map (MulAut.conj n⁻¹).toMonoidHom, ?_, ?_, ?_, ?_⟩
    · rintro _ ⟨y, hy, rfl⟩
      change MulAut.conj n⁻¹ y * MulAut.conj n⁻¹ y = 1
      rw [← map_mul, h1 y hy, map_one]
    · rintro _ ⟨y, hy, rfl⟩ _ ⟨z, hz, rfl⟩
      change MulAut.conj n⁻¹ y * MulAut.conj n⁻¹ z = MulAut.conj n⁻¹ z * MulAut.conj n⁻¹ y
      rw [← map_mul, ← map_mul, h2 y hy z hz]
    · rw [Subgroup.card_map_of_injective (MulAut.conj n⁻¹).injective]
      exact h3
    · rintro _ ⟨y, hy, rfl⟩
      change (MulAut.conj s * fld) (MulAut.conj n⁻¹ y) = MulAut.conj n⁻¹ y
      rw [hθ', MulAut.mul_apply, MulAut.mul_apply]
      have e : MulAut.conj n (MulAut.conj n⁻¹ y) = y := by
        rw [MulAut.conj_apply, MulAut.conj_apply]
        group
      rw [e, h4 y hy]

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
