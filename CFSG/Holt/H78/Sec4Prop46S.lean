module

public import CFSG.Holt.H78.Sec4Prop46A
import CFSG.Holt.H78.Prelim
import CFSG.Holt.H78.OddCoreMinimal
import CFSG.Holt.H78.Conjugacy
import CFSG.Holt.H78.Sec4Lemma42
import CFSG.Holt.H78.Sec4Prop46BRec

public section

namespace CFSG.Holt.H78

open MulAction CFSG.Holt CFSG.Open
open scoped Pointwise

section Helpers

variable {G : Type*} [Group G]

private theorem mem_centralizer_zpowers_of_commute {g x : G} (h : Commute g x) :
    g ∈ Subgroup.centralizer (Subgroup.zpowers x : Set G) := by
  refine Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  exact (h.symm.zpow_left k).eq

private theorem commute_of_mem_centralizer_zpowers {g x : G}
    (h : g ∈ Subgroup.centralizer (Subgroup.zpowers x : Set G)) : Commute g x :=
  (Subgroup.mem_centralizer_iff.mp h x (Subgroup.mem_zpowers x)).symm

theorem exists_normal_minimal_le [Finite G] {Q : Subgroup G} (hQn : Q.Normal) (hQ : Q ≠ ⊥) :
    ∃ P : Subgroup G, P.Normal ∧ P ≠ ⊥ ∧ P ≤ Q ∧ ∀ R ≤ P, R.Normal → R = ⊥ ∨ R = P := by
  classical
  have hex : ∃ n, ∃ R : Subgroup G, R.Normal ∧ R ≠ ⊥ ∧ R ≤ Q ∧ Nat.card R = n :=
    ⟨_, Q, hQn, hQ, le_rfl, rfl⟩
  obtain ⟨P, hPn, hP1, hPQ, hPc⟩ := Nat.find_spec hex
  refine ⟨P, hPn, hP1, hPQ, fun R hRP hRn => ?_⟩
  by_cases hR : R = ⊥
  · exact Or.inl hR
  · refine Or.inr (Subgroup.eq_of_le_of_card_ge hRP ?_)
    rw [hPc]
    exact Nat.find_min' hex ⟨R, hRn, hR, hRP.trans hPQ, rfl⟩

end Helpers

section TypeL

variable {G : Type} [Group G] [Finite G] {Ω : Type} [Fintype Ω] [DecidableEq Ω] [MulAction G Ω]
  [FaithfulSMul G Ω] {α : Ω} {v : G}

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
private theorem mem_fixSet_zpowers_iff_smul {ω : Ω} :
    ω ∈ fixSet Ω (Subgroup.zpowers v) ↔ v • ω = ω := by
  rw [fixSet_zpowers, mem_fixedBy]

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
private theorem exists_longInvAt_commute (hv : IsTypeL G Ω α v) :
    ∃ t ∈ longInvAt G Ω α, ∃ u ∈ longInvAt G Ω α, Commute t v ∧ t * v = u := by
  obtain ⟨t, ht, u, hu, -, hc, htuv, -⟩ := hv
  refine ⟨t, ht, u, hu, htuv ▸ (Commute.refl t).mul_right hc, ?_⟩
  rw [← htuv, ← mul_assoc, mul_self_eq_one_of_mem_longInv ht.1, one_mul]

theorem Sec4Setting.longInvAt_typeLSection_nonempty (hS : Sec4Setting G Ω)
    (hv : IsTypeL G Ω α v) {a : fixSet Ω (Subgroup.zpowers v)} (ha : (a : Ω) = α) :
    (longInvAt (typeLSection G Ω v) (fixSet Ω (Subgroup.zpowers v)) a).Nonempty := by
  obtain ⟨t, ht, -, -, htv, -⟩ := exists_longInvAt_commute hv
  have htC := mem_centralizer_zpowers_of_commute htv
  exact ⟨centralizerImageElt (Ω := Ω) htC,
    (hS.mem_longInvAt_centralizerImage_iff (isPGroup_zpowers_of_orderOf_eq_two hv.orderOf_eq_two)
      (three_le_card_fixSet_of_isTypeL hS.star hv) _).mpr ⟨t, ha ▸ ht, htC, fun _ => rfl⟩⟩

theorem Sec4Setting.existsUnique_mem_holtDelta_smul_eq (hS : Sec4Setting G Ω)
    (hv : IsTypeL G Ω α v) {P : Subgroup (typeLSection G Ω v)} (hPn : P.Normal)
    (hPmin : ∀ R ≤ P, R.Normal → R = ⊥ ∨ R = P)
    (hPO : P ≤ CFSG.pPrimeCore 2 (typeLSection G Ω v)) {β : Ω}
    (hβ : β ∈ p46Orbit G Ω v P α) (hβα : β ≠ α) :
    ∃! γ, γ ∈ holtDelta G Ω α β ∧ v • γ = γ := by
  obtain ⟨p, hp, a, ha, hpa⟩ := hβ
  have hPc := commute_of_minimal_normal_of_odd hPn hPmin
    (Odd.of_dvd_nat odd_card_pPrimeCore_two (Subgroup.card_dvd_of_le hPO))
  obtain ⟨γ, -, hΔ, -⟩ := holtDelta_eq_singleton_of_mem_orbit hPn hPc
    (hS.longInvAt_typeLSection_nonempty hv ha) (⟨⟨p, hp⟩, rfl⟩ : p • a ∈ orbit P a)
  have hab : a ≠ p • a := fun h => hβα (by rw [← hpa, ← h, ha])
  rw [hS.holtDelta_centralizerImage (isPGroup_zpowers_of_orderOf_eq_two hv.orderOf_eq_two)
    (three_le_card_fixSet_of_isTypeL hS.star hv) hab, ha, hpa] at hΔ
  refine ⟨γ, ⟨(Set.ext_iff.mp hΔ γ).mpr rfl, mem_fixSet_zpowers_iff_smul.mp γ.2⟩,
    fun δ ⟨hδ, hvδ⟩ => ?_⟩
  exact congrArg Subtype.val ((Set.ext_iff.mp hΔ
    ⟨δ, mem_fixSet_zpowers_iff_smul.mpr hvδ⟩).mp hδ)

theorem Sec4Setting.exists_w_of_isTypeL (hS : Sec4Setting G Ω)
    (hv : IsTypeL G Ω α v) {β : Ω} (hvβ : v • β = β) :
    ∃ w ∈ longInvSwap G Ω α β, Commute w v ∧ w * v ∈ longInv G Ω := by
  obtain ⟨t, ht, u, hu, htv, htvu⟩ := exists_longInvAt_commute hv
  have htC := mem_centralizer_zpowers_of_commute htv
  have hK := hS.star_typeLSection hv
  have hKB := hS.holtTheorem1Below_typeLSection hv
  have htK : centralizerImageElt (Ω := Ω) htC ∈
      longInv (typeLSection G Ω v) (fixSet Ω (Subgroup.zpowers v)) :=
    (hS.mem_longInv_centralizerImage_iff (isPGroup_zpowers_of_orderOf_eq_two hv.orderOf_eq_two)
      (three_le_card_fixSet_of_isTypeL hS.star hv) _).mpr ⟨t, ht.1, htC, fun _ => rfl⟩
  set a : fixSet Ω (Subgroup.zpowers v) := ⟨α, mem_fixSet_zpowers_iff_smul.mpr hv.smul_eq⟩
  obtain ⟨-, s, hs, -⟩ := holtDelta_nonempty hK a ⟨β, mem_fixSet_zpowers_iff_smul.mpr hvβ⟩
  obtain ⟨⟨_, c, rfl⟩, hk⟩ := exists_conj_eq_of_mem_longInv hK hKB htK hs.1
  have hcv : Commute (c : G) v := commute_of_mem_centralizer_zpowers c.2
  refine ⟨(c : G) * t * (c : G)⁻¹, ⟨conj_mem_longInv ht.1 _, ?_⟩,
    commute_of_mem_centralizer_zpowers (mul_mem (mul_mem c.2 htC) (inv_mem c.2)), ?_⟩
  · have h := congrArg (fun z : typeLSection G Ω v =>
      ((z : Equiv.Perm (fixSet Ω (Subgroup.zpowers v))) a : Ω)) hk
    rw [mul_smul, mul_smul]
    exact h.trans (congrArg Subtype.val hs.2)
  · have : (c : G) * t * (c : G)⁻¹ * v = (c : G) * u * (c : G)⁻¹ := by
      rw [mul_assoc _ (c : G)⁻¹, ← hcv.symm.inv_right.eq, ← mul_assoc, mul_assoc (c : G) t, htvu]
    rw [this]
    exact conj_mem_longInv hu.1 _

end TypeL

section Coordinates

variable {K X : Type*} [Group K] [MulAction K X] (D : HoltData K X)

theorem HoltData.eq_coord_of_rho_apply_eq (hO : jOddCore K X = ⊥) {h : jHull K X} {γ : X}
    (hγ : (h : K) • γ = γ) (hu : ∀ δ : X, (h : K) • δ = δ → δ = γ) {i : D.ι} {x : D.Ψc i}
    (hx : D.ρ i h x = x) : x = D.coord γ i := by
  obtain ⟨δ, hδ⟩ := D.coord_surjective (Function.update (D.coord γ) i x)
  have hfix : (h : K) • δ = δ := D.coord_injective hO (funext fun j => by
    rw [D.coord_smul h δ j, hδ]
    by_cases hj : j = i
    · subst hj
      rw [Function.update_self, hx]
    · rw [Function.update_of_ne hj, ← D.coord_smul, hγ])
  have := congrFun hδ i
  rw [Function.update_self] at this
  rw [← this, hu δ hfix]

theorem HoltData.rho_mem_longInv_perm (hO : jOddCore K X = ⊥) {h : jHull K X} (h2 : h * h = 1)
    {γ : X} (hγ : (h : K) • γ = γ) (hu : ∀ δ : X, (h : K) • δ = δ → δ = γ) (i : D.ι) :
    D.ρ i h ∈ longInv (Equiv.Perm (D.Ψc i)) (D.Ψc i) := by
  have hfix : D.ρ i h (D.coord γ i) = D.coord γ i := by rw [← D.coord_smul, hγ]
  refine ⟨orderOf_eq_prime (by rw [sq, ← map_mul, h2, map_one]) fun h1 => ?_,
    D.coord γ i, hfix, fun x hx => D.eq_coord_of_rho_apply_eq hO hγ hu hx⟩
  have hall : ∀ x : D.Ψc i, x = D.coord γ i := fun x =>
    D.eq_coord_of_rho_apply_eq hO hγ hu (by rw [h1]; rfl)
  have h5 := D.five_le_card i
  have := Fintype.card_le_one_iff.mpr fun x y => (hall x).trans (hall y).symm
  omega

theorem card_mod_four_of_mul_mem_longInv_perm {Ψ : Type*} [Fintype Ψ] [DecidableEq Ψ]
    {σ τ : Equiv.Perm Ψ} (hσ : σ ∈ longInv (Equiv.Perm Ψ) Ψ)
    (hτ : τ ∈ longInv (Equiv.Perm Ψ) Ψ) (hστ : σ * τ ∈ longInv (Equiv.Perm Ψ) Ψ) :
    Fintype.card Ψ % 4 = 1 := by
  rw [← mem_alternatingGroup_iff_of_mem_longInv_perm hστ, Equiv.Perm.mem_alternatingGroup,
    Equiv.Perm.sign_mul, sign_eq_of_mem_longInv_perm hσ hτ, Int.units_mul_self]

end Coordinates

section TwoPoint

variable {G : Type} [Group G] [Finite G] {Ω : Type} [Fintype Ω] [DecidableEq Ω] [MulAction G Ω]
  [FaithfulSMul G Ω] {α β γ : Ω} {w v : G}

private theorem ncard_setOf_eq_one_of_unique {Y : Type*} {b : Set Y} {p : Y → Prop} {y₀ : Y}
    (h0 : y₀ ∈ b) (hp : p y₀) (hu : ∀ y ∈ b, p y → y = y₀) : {y | y ∈ b ∧ p y}.ncard = 1 :=
  Set.ncard_eq_one.mpr ⟨y₀, Set.ext fun y => ⟨fun h => hu y h.1 h.2, fun h => h ▸ ⟨h0, hp⟩⟩⟩

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem smul_eq_of_mem_longInvSwap_of_unique (hw : w ∈ longInvSwap G Ω α β) (hwv : Commute w v)
    (hγ : γ ∈ holtDelta G Ω α β) (hvγ : v • γ = γ)
    (hγu : ∀ δ ∈ holtDelta G Ω α β, v • δ = δ → δ = γ) : w • γ = γ := by
  refine hγu _ ?_ ?_
  · rw [← mem_stabilizer_iff.mp (mem_stabilizer_holtDelta_of_mem_longInvSwap hw)]
    exact Set.smul_mem_smul_set hγ
  · rw [← mul_smul, ← hwv.eq, mul_smul, hvγ]

omit [Finite G] [FaithfulSMul G Ω] in
theorem Sec4Setting.jOddCore_twoPointSection_eq_bot_of_unique (hS : Sec4Setting G Ω)
    (hαβ : α ≠ β) (h3 : 3 ≤ Nat.card (holtDelta G Ω α β)) (hw : w ∈ longInvSwap G Ω α β)
    (hvα : v • α = α) (hvβ : v • β = β) (hv2 : v * v = 1) (hwv : Commute w v)
    (hwvJ : w * v ∈ longInv G Ω) (hγ : γ ∈ holtDelta G Ω α β) (hvγ : v • γ = γ)
    (hγu : ∀ δ ∈ holtDelta G Ω α β, v • δ = δ → δ = γ) :
    jOddCore (twoPointSection G Ω α β) (holtDelta G Ω α β) = ⊥ := by
  set N := jOddCore (twoPointSection G Ω α β) (holtDelta G Ω α β)
  have hN : Odd (Nat.card N) := odd_card_jOddCore
  have hwγ := smul_eq_of_mem_longInvSwap_of_unique hw hwv hγ hvγ hγu
  have hwvγ : w • v • γ = γ := by rw [hvγ, hwγ]
  have hwS : w ∈ stabilizer G ({α, β} : Set Ω) := mem_stabilizer_pair_of_mem_longInvSwap hw
  have hvS : v ∈ stabilizer G ({α, β} : Set Ω) :=
    stabilizer_inf_le_stabilizer_pair α β (Subgroup.mem_inf.mpr ⟨hvα, hvβ⟩)
  set wD : twoPointSection G Ω α β := twoPointElt hwS
  set vD : twoPointSection G Ω α β := twoPointElt hvS
  set γΔ : holtDelta G Ω α β := ⟨γ, hγ⟩
  have hF := ncard_fixed_orbit_mul (N := N) hN (γ := γΔ) (x := wD) (y := vD)
    (Subtype.ext hwγ) (Subtype.ext hvγ)
    (fun δ _ => Subtype.ext (show w • w • (δ : Ω) = δ by
      rw [← mul_smul, mul_self_eq_one_of_mem_longInv hw.1, one_smul]))
    (fun δ _ => Subtype.ext (show v • v • (δ : Ω) = δ by rw [← mul_smul, hv2, one_smul]))
    (fun δ _ => Subtype.ext (show w • v • (δ : Ω) = v • w • (δ : Ω) by
      rw [← mul_smul, ← mul_smul, hwv.eq]))
  rw [ncard_setOf_eq_one_of_unique (p := fun δ => wD • δ = δ) (mem_orbit_self γΔ)
      (Subtype.ext hwγ) (fun δ _ h => Subtype.ext (hw.1.2.unique (congrArg Subtype.val h) hwγ)),
    ncard_setOf_eq_one_of_unique (p := fun δ => vD • δ = δ) (mem_orbit_self γΔ)
      (Subtype.ext hvγ) (fun δ _ h => Subtype.ext (hγu _ δ.2 (congrArg Subtype.val h))),
    ncard_setOf_eq_one_of_unique (p := fun δ => wD • vD • δ = δ) (mem_orbit_self γΔ)
      (Subtype.ext hwvγ)
      (fun δ _ h => Subtype.ext (hwvJ.2.unique (by rw [mul_smul]; exact congrArg Subtype.val h)
        (by rw [mul_smul]; exact hwvγ))),
    ncard_setOf_eq_one_of_unique (p := fun δ => wD • δ = δ ∧ vD • δ = δ) (mem_orbit_self γΔ)
      ⟨Subtype.ext hwγ, Subtype.ext hvγ⟩
      (fun δ _ h => Subtype.ext (hw.1.2.unique (congrArg Subtype.val h.1) hwγ))] at hF
  have hb : orbit N γΔ = {γΔ} := by
    have h1 : (orbit N γΔ).ncard = 1 := by
      rw [one_mul, one_mul, one_pow, mul_one] at hF
      exact hF.symm
    obtain ⟨c, hc⟩ := Set.ncard_eq_one.mp h1
    rw [hc, (Set.mem_singleton_iff.mp (hc ▸ mem_orbit_self γΔ : γΔ ∈ ({c} : Set _)))]
  have hle : N ≤ stabilizer (twoPointSection G Ω α β) γΔ := fun n hn =>
    mem_stabilizer_iff.mpr (Set.mem_singleton_iff.mp (hb ▸ mem_orbit γΔ (⟨n, hn⟩ : N)))
  have := (hS.star_twoPoint hαβ h3).isPretransitive
  exact eq_bot_of_normal_le_stabilizer hle

omit [FaithfulSMul G Ω] in
theorem Sec4Setting.isNaturalSE_twoPointJ_of_holtData
    (hS : Sec4Setting G Ω) (D : HoltData (twoPointSection G Ω α β) (holtDelta G Ω α β))
    (hO : jOddCore (twoPointSection G Ω α β) (holtDelta G Ω α β) = ⊥) {i₀ : D.ι}
    (hι : ∀ j, j = i₀) (hSE : IsNaturalSE (D.M i₀)) : IsNaturalSE (twoPointJ G Ω α β) := by
  have hbij : Function.Bijective fun δ : holtDelta G Ω α β => D.coord δ i₀ :=
    ⟨fun δ δ' h => D.coord_injective hO (funext fun j => by rw [hι j]; exact h),
      fun c => D.exists_coord_apply_eq i₀ c⟩
  have hM := D.map_permCongrHom_map_L (Equiv.ofBijective _ hbij) fun h δ => D.coord_smul h δ i₀
  obtain ⟨n, j, e, hA⟩ := isNaturalSE_iff.mp hSE
  have hAX := IsBenderAction.of_map_permCongrHom (Equiv.ofBijective _ hbij)
    (by rw [hM]; exact hA)
  have hLJ : D.L i₀ = jHull (twoPointSection G Ω α β) (holtDelta G Ω α β) :=
    le_antisymm (D.L_le i₀) (D.jHull_le_L_of_isNaturalSE hO hι hSE)
  have hhom : MulAction.toPermHom (twoPointSection G Ω α β) (holtDelta G Ω α β) =
      (twoPointSection G Ω α β).subtype := MonoidHom.ext fun h => Equiv.ext fun x => rfl
  rw [hS.twoPointJ_eq_map_jHull, ← hhom, ← hLJ]
  exact isNaturalSE_iff.mpr ⟨n, j, e, hAX⟩

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
private abbrev twoPointHullElt (hG : IsStarGroup G Ω) {c : G}
    (hc : c ∈ Subgroup.closure (longInvSwap G Ω α β)) :
    jHull (twoPointSection G Ω α β) (holtDelta G Ω α β) :=
  ⟨twoPointElt (closure_longInvSwap_le_stabilizer_pair α β hc), twoPointElt_mem_jHull hG hc⟩

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
private theorem jHull_twoPoint_ext {h h' : jHull (twoPointSection G Ω α β) (holtDelta G Ω α β)}
    (H : ∀ δ : holtDelta G Ω α β, (((h : twoPointSection G Ω α β) • δ : holtDelta G Ω α β) : Ω) =
      (((h' : twoPointSection G Ω α β) • δ : holtDelta G Ω α β) : Ω)) : h = h' :=
  Subtype.ext (Subtype.ext (Equiv.ext fun δ => Subtype.ext (H δ)))

theorem Sec4Setting.isTypeAAt_or_isTypeBAt_of_unique
    (hS : Sec4Setting G Ω) (hαβ : α ≠ β) (h1 : 1 < Nat.card (holtDelta G Ω α β))
    (hw : w ∈ longInvSwap G Ω α β) (hvα : v • α = α) (hvβ : v • β = β) (hv2 : v * v = 1)
    (hwv : Commute w v) (hwvJ : w * v ∈ longInv G Ω) (hγ : γ ∈ holtDelta G Ω α β)
    (hvγ : v • γ = γ) (hγu : ∀ δ ∈ holtDelta G Ω α β, v • δ = δ → δ = γ) :
    IsTypeAAt G Ω α β ∨ IsTypeBAt G Ω α β := by
  have h3 : 3 ≤ Nat.card (holtDelta G Ω α β) := by
    obtain ⟨k, hk⟩ := hS.star.odd_card_holtDelta α β
    omega
  have hO := hS.jOddCore_twoPointSection_eq_bot_of_unique hαβ h3 hw hvα hvβ hv2 hwv hwvJ hγ hvγ
    hγu
  obtain ⟨D⟩ := hS.holtData_twoPoint h3
  have hwγ := smul_eq_of_mem_longInvSwap_of_unique hw hwv hγ hvγ hγu
  have hwvs : w * v ∈ longInvSwap G Ω α β := ⟨hwvJ, by rw [mul_smul, hvα]; exact hw.2⟩
  have hw2 := mul_self_eq_one_of_mem_longInv hw.1
  have hvcl : v ∈ Subgroup.closure (longInvSwap G Ω α β) := by
    have := mul_mem (Subgroup.subset_closure hw) (Subgroup.subset_closure hwvs)
    rwa [← mul_assoc, hw2, one_mul] at this
  set γΔ : holtDelta G Ω α β := ⟨γ, hγ⟩
  set wH := twoPointHullElt hS.star (Subgroup.subset_closure hw)
  set uH := twoPointHullElt hS.star (Subgroup.subset_closure hwvs)
  set vH := twoPointHullElt hS.star hvcl
  have hmod4 : ∀ i, Fintype.card (D.Ψc i) % 4 = 1 := fun i => by
    have hwi := D.rho_mem_longInv_perm hO (h := wH)
      (jHull_twoPoint_ext fun δ => show w • w • (δ : Ω) = δ by rw [← mul_smul, hw2, one_smul])
      (γ := γΔ) (Subtype.ext hwγ)
      (fun δ h => Subtype.ext (hw.1.2.unique (congrArg Subtype.val h) hwγ)) i
    have hui := D.rho_mem_longInv_perm hO (h := uH)
      (jHull_twoPoint_ext fun δ => show (w * v) • (w * v) • (δ : Ω) = δ by
        rw [← mul_smul, mul_self_eq_one_of_mem_longInv hwvJ, one_smul])
      (γ := γΔ) (Subtype.ext (show (w * v) • γ = γ by rw [mul_smul, hvγ, hwγ]))
      (fun δ h => Subtype.ext (hwvJ.2.unique (congrArg Subtype.val h)
        (by rw [mul_smul, hvγ, hwγ]))) i
    have hvi := D.rho_mem_longInv_perm hO (h := vH)
      (jHull_twoPoint_ext fun δ => show v • v • (δ : Ω) = δ by rw [← mul_smul, hv2, one_smul])
      (γ := γΔ) (Subtype.ext hvγ)
      (fun δ h => Subtype.ext (hγu _ δ.2 (congrArg Subtype.val h))) i
    have hprod : wH * uH = vH := jHull_twoPoint_ext fun δ =>
      show w • (w * v) • (δ : Ω) = v • δ by rw [← mul_smul, ← mul_assoc, hw2, one_mul]
    exact card_mod_four_of_mul_mem_longInv_perm hwi hui (by rw [← map_mul, hprod]; exact hvi)
  by_cases hB1 : ∃ i, IsNaturalSE (D.M i) ∧ Fintype.card (D.Ψc i) ≠ 5
  · obtain ⟨i, hi, hi5⟩ := hB1
    obtain ⟨hT, hr⟩ := hS.lemma_4_2 hαβ D i hi hi5
    exact Or.inr ⟨hS.isNaturalSE_twoPointJ_of_holtData D hO
      (fun j => Fintype.card_le_one_iff.mp (hr hO).le j i) hi, hT⟩
  by_cases hB2 : Fintype.card D.ι = 1 ∧ (∃ i, Fintype.card (D.Ψc i) = 5) ∧
      Odd (Nat.card (twoPointKernel G Ω α β))
  · obtain ⟨hr, ⟨i, hi5⟩, hT⟩ := hB2
    have hi : IsNaturalSE (D.M i) := by
      rcases D.factor i with h | h
      · exact absurd h.2 (by omega)
      · exact h
    exact Or.inr ⟨hS.isNaturalSE_twoPointJ_of_holtData D hO
      (fun j => Fintype.card_le_one_iff.mp hr.le j i) hi, hT⟩
  have halt : ∀ i, factorImage _ _ (D.L i) (D.ρ i) = alternatingGroup (D.Ψc i) := fun i => by
    rcases D.factor i with h | h
    · exact h.1
    · exact h.eq_alternatingGroup_of_card_eq_five (by
        by_contra h5
        exact hB1 ⟨i, h, h5⟩)
  exact Or.inl ⟨⟨D, hO, halt, hmod4, fun hr i hi5 hT => hB2 ⟨hr, ⟨i, hi5⟩, hT⟩⟩⟩

end TwoPoint

section Setup

variable {G : Type} [Group G] [Finite G] {Ω : Type} [Fintype Ω] [DecidableEq Ω] [MulAction G Ω]
  [FaithfulSMul G Ω] {α : Ω} {v : G}

theorem Sec4Setting.prop46Setup (hS : Sec4Setting G Ω)
    (hv : IsTypeL G Ω α v) {P : Subgroup (typeLSection G Ω v)} (hPn : P.Normal)
    (hPmin : ∀ R ≤ P, R.Normal → R = ⊥ ∨ R = P)
    (hPO : P ≤ CFSG.pPrimeCore 2 (typeLSection G Ω v)) : Prop46Setup G Ω α v P := by
  have hvC : ∀ β ∈ p46Orbit G Ω v P α, v • β = β := by
    rintro β ⟨p, -, a, -, rfl⟩
    exact mem_fixSet_zpowers_iff_smul.mp (p • a).2
  have hv2 : v * v = 1 := by rw [← sq, ← hv.orderOf_eq_two, pow_orderOf_eq_one]
  refine ⟨hv, hPn, hPmin, hPO,
    fun β hβ hβα => hS.existsUnique_mem_holtDelta_smul_eq hv hPn hPmin hPO hβ hβα,
    fun β hβ _ => hS.exists_w_of_isTypeL hv (hvC β hβ), fun β hβ hβα h1 => ?_⟩
  obtain ⟨γ, ⟨hγ, hvγ⟩, hγu⟩ := hS.existsUnique_mem_holtDelta_smul_eq hv hPn hPmin hPO hβ hβα
  obtain ⟨w, hw, hwv, hwvJ⟩ := hS.exists_w_of_isTypeL hv (hvC β hβ)
  exact hS.isTypeAAt_or_isTypeBAt_of_unique (Ne.symm hβα) h1 hw hv.smul_eq (hvC β hβ) hv2 hwv
    hwvJ hγ hvγ fun δ hδ h => hγu δ ⟨hδ, h⟩

end Setup

end CFSG.Holt.H78
