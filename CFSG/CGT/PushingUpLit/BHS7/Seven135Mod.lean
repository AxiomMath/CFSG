module

public import CFSG.CGT.PushingUpLit.BHS6.BlockStructure

public section

namespace CFSG.CGT.PushingUpLit.BHS7

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.Quasithin.G6 CFSG.QuasithinUnique
  CFSG.QuasithinUnique.Setup.Campbell CFSG.RankThree.PartOne CFSG.CGT.PushingUpLit
  CFSG.CGT.PushingUpLit.BHS CFSG.CGT.PushingUpLit.BHS6
open scoped commutatorElement

section Module

variable {W : Type} [CommGroup W]

theorem s135_apply_mem_fixV {U : Subgroup (MulAut W)} {g : MulAut W}
    (hgU : g ∈ Subgroup.normalizer (U : Set (MulAut W))) {w : W} (hw : w ∈ fixV U) :
    g w ∈ fixV U :=
  CFSG.Quasithin.fixV_apply_mem_of_mem_normalizer hgU hw


section SL

variable [Finite W] {F : Type} [Field F] [Finite F] [CharP F 2] {E : Subgroup (MulAut W)}

theorem s135_sl_main (D : SLNatData E F) (hF : 2 ≤ Nat.card F)
    {U : Subgroup (MulAut W)} (hUE : U ≤ E) (hUne : U ≠ ⊥) (hcardU : Nat.card U = Nat.card F)
    (hW : Nat.card W = Nat.card U * Nat.card (fixV U)) (hUq : IsQuadratic U)
    {Q : Subgroup (MulAut W)} (hQ : IsPGroup 2 Q) (hUQ : U ≤ Q)
    (hQN : Q ≤ Subgroup.normalizer (E : Set (MulAut W)))
    {g : MulAut W} (hgQ : g ∈ Q) (hgU : g ∈ Subgroup.normalizer (U : Set (MulAut W)))
    (hg1 : g ≠ 1) :
    ∃ w : W, g w * w⁻¹ ∈ fixV U ∧ g w * w⁻¹ ∉ fixV E := by
  classical
  by_cases hα : ∃ w₁ ∈ fixV U, g w₁ * w₁⁻¹ ∉ fixV E
  · obtain ⟨w₁, hw₁, hne⟩ := hα
    exact ⟨w₁, (fixV U).mul_mem (s135_apply_mem_fixV hgU hw₁) ((fixV U).inv_mem hw₁), hne⟩
  push Not at hα
  obtain ⟨v₀, hv₀, hline⟩ := exists_line_beta_fixV D hF hUE hUne hcardU hW
  have hgN : g ∈ Subgroup.normalizer (E : Set (MulAut W)) := hQN hgQ
  have hgE : g ∈ E := by
    obtain ⟨k, hk⟩ := hQ ⟨g, hgQ⟩
    have hx : (⟨g, hgN⟩ : ↥(Subgroup.normalizer (E : Set (MulAut W)))) ^ 2 ^ k = 1 := by
      apply Subtype.ext
      simpa using congrArg Subtype.val hk
    refine mem_of_psi_fixes_line D ⟨g, hgN⟩ hx hv₀ fun c => ?_
    obtain ⟨w, hw, hwβ⟩ := hline c
    have h1 := D.psi_spec ⟨g, hgN⟩ w
    have h2 : D.β (g w) = D.β w := by
      have := (D.ker_iff _).mpr (hα w hw)
      rwa [map_mul, map_inv, mul_inv_eq_one] at this
    rw [h2, hwβ] at h1
    simpa using h1.symm
  have hgU' : g ∈ U := by
    have hsup : U ⊔ Subgroup.zpowers g ≤ E := sup_le hUE ((Subgroup.zpowers_le).mpr hgE)
    have hsupQ : U ⊔ Subgroup.zpowers g ≤ Q := sup_le hUQ ((Subgroup.zpowers_le).mpr hgQ)
    have hle := card_le_of_isPGroup_of_slNatData D hsup (hQ.to_le hsupQ)
    have : U = U ⊔ Subgroup.zpowers g :=
      Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [hcardU]; exact hle)
    rw [this]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers g)
  have hnt : ∃ w : W, D.β (g w * w⁻¹) ≠ 1 := by
    by_contra hcon
    push Not at hcon
    apply hg1
    have h1 : ∀ w : W, D.β (g w) = D.β w := fun w => by
      have := hcon w
      rwa [map_mul, map_inv, mul_inv_eq_one] at this
    set e : ↥E := ⟨g, hgE⟩ with he
    have h2 : D.θ e = 1 := by
      apply eq_one_of_forall_smul_vec
      intro v
      obtain ⟨w, hw⟩ := D.surj (Multiplicative.ofAdd v)
      have h3 := D.equivar' e w
      rw [hw] at h3
      have h4 : D.β ((e : MulAut W) w) = D.β w := h1 w
      rw [h4, hw] at h3
      simpa [Matrix.SpecialLinearGroup.smul_def] using h3.symm
    have h3 : e = 1 := D.θ.injective (by rw [h2, map_one])
    exact congrArg Subtype.val h3
  obtain ⟨w, hw⟩ := hnt
  refine ⟨w, ?_, fun hmem => hw ((D.ker_iff _).mpr hmem)⟩
  exact hUq (Subgroup.subset_closure ⟨g, hgU', w, rfl⟩)

end SL

section A3

variable [Finite W]

theorem s135_a3_main (hcard : Nat.card W = 4) {E U : Subgroup (MulAut W)} (hfixE : fixV E = ⊥)
    (hUne : U ≠ ⊥) (hfixU : ∃ w ∈ fixV U, w ≠ 1) {g : MulAut W}
    (hgU : g ∈ Subgroup.normalizer (U : Set (MulAut W))) (hg1 : g ≠ 1) :
    ∃ w : W, g w * w⁻¹ ∈ fixV U ∧ g w * w⁻¹ ∉ fixV E := by
  classical
  obtain ⟨w₀, hw₀⟩ : ∃ w₀ : W, g w₀ ≠ w₀ := by
    by_contra hcon
    push Not at hcon
    exact hg1 (MulEquiv.ext fun w => by rw [hcon w]; rfl)
  have hnotE : ∀ r : W, r ≠ 1 → r ∉ fixV E := fun r hr hmem => hr (by
    rw [hfixE] at hmem
    exact Subgroup.mem_bot.mp hmem)
  by_cases hα : ∃ w₁ ∈ fixV U, g w₁ ≠ w₁
  · obtain ⟨w₁, hw₁, hne⟩ := hα
    exact ⟨w₁, (fixV U).mul_mem (s135_apply_mem_fixV hgU hw₁) ((fixV U).inv_mem hw₁),
      hnotE _ fun h => hne (mul_inv_eq_one.mp h)⟩
  push Not at hα
  refine ⟨w₀, ?_, hnotE _ fun h => hw₀ (mul_inv_eq_one.mp h)⟩
  have hne_top : fixV U ≠ ⊤ := by
    intro htop
    obtain ⟨⟨u, hu⟩, hu1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hUne
    have hu1' : u ≠ 1 := fun h => hu1 (Subtype.ext h)
    obtain ⟨w, hw⟩ : ∃ w : W, u w ≠ w := by
      by_contra hcon
      push Not at hcon
      exact hu1' (MulEquiv.ext fun w => by rw [hcon w]; rfl)
    have : w ∈ fixV U := by rw [htop]; trivial
    exact hw (this u hu)
  have hdvd : Nat.card (fixV U) ∣ 4 := hcard ▸ Subgroup.card_subgroup_dvd_card _
  have hgt : 1 < Nat.card (fixV U) := by
    rw [Subgroup.one_lt_card_iff_ne_bot, Ne, Subgroup.eq_bot_iff_forall]
    push Not
    obtain ⟨w, hw, hw1⟩ := hfixU
    exact ⟨w, hw, hw1⟩
  have hlt4 : Nat.card (fixV U) ≠ 4 := fun h => hne_top (Subgroup.eq_top_of_card_eq _ (by
    rw [h, hcard]))
  have hcard2 : Nat.card (fixV U) = 2 := by
    have hle : Nat.card (fixV U) ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
    interval_cases h : Nat.card (fixV U) <;> first | rfl | omega
  have hidx : (fixV U).index = 2 := by
    have := Subgroup.card_mul_index (fixV U)
    rw [hcard2, hcard] at this
    omega
  obtain ⟨a, ha⟩ := Subgroup.index_eq_two_iff.mp hidx
  have hcoset : ∀ b : W, b ∉ fixV U → b * a ∈ fixV U := fun b hb => by
    rcases ha b with ⟨h1, -⟩ | ⟨h2, -⟩
    · exact h1
    · exact absurd h2 hb
  by_cases hw : w₀ ∈ fixV U
  · exact absurd (hα w₀ hw) hw₀
  have hgw : g w₀ ∉ fixV U := by
    intro hmem
    apply hw
    have := hα _ hmem
    have h2 : g w₀ = w₀ := by
      have h3 : g⁻¹ (g w₀) = g w₀ := by
        have := hα (g w₀) hmem
        calc g⁻¹ (g w₀) = g⁻¹ (g (g w₀)) := by rw [this]
          _ = g w₀ := by simp
      have h4 : w₀ = g w₀ := by simpa using h3
      exact h4.symm
    exact h2 ▸ hmem
  have h1 := hcoset _ hgw
  have h2 := hcoset _ hw
  have := (fixV U).mul_mem h1 ((fixV U).inv_mem h2)
  convert this using 1
  group

end A3

section Alt

omit [CommGroup W] in
theorem s135_swap_comm {n : ℕ} {x y : Fin n} (hxy : x ≠ y) (v : ↥(coreMod n)) :
    coreAct n (Equiv.swap x y) v * v⁻¹ = 1 ∨
      coreAct n (Equiv.swap x y) v * v⁻¹ = pairVec x y := by
  classical
  have hcoord : ∀ i, vcoord (coreAct n (Equiv.swap x y) v * v⁻¹) i =
      vcoord v (Equiv.swap x y i) + vcoord v i := by
    intro i
    rw [vcoord_mul, vcoord_inv, vcoord_coreAct, Equiv.swap_inv]
  by_cases h : vcoord v x = vcoord v y
  · left
    refine vcoord_ext fun i => ?_
    rw [hcoord, vcoord_one]
    by_cases hix : i = x
    · rw [hix, Equiv.swap_apply_left, ← h]
      exact CharTwo.add_self_eq_zero _
    · by_cases hiy : i = y
      · rw [hiy, Equiv.swap_apply_right, h]
        exact CharTwo.add_self_eq_zero _
      · rw [Equiv.swap_apply_of_ne_of_ne hix hiy]
        exact CharTwo.add_self_eq_zero _
  · right
    have h1 : vcoord v x + vcoord v y = 1 := by
      generalize vcoord v x = a at *
      generalize vcoord v y = b at *
      revert a b
      decide
    refine vcoord_ext fun i => ?_
    rw [hcoord, vcoord_pairVec]
    by_cases hix : i = x
    · have e1 : (if x = x then (1 : ZMod 2) else 0) + (if x = y then 1 else 0) = 1 := by
        simp [hxy]
      rw [hix, Equiv.swap_apply_left, e1, add_comm]
      exact h1
    · by_cases hiy : i = y
      · have e1 : (if y = x then (1 : ZMod 2) else 0) + (if y = y then 1 else 0) = 1 := by
          simp [Ne.symm hxy]
        rw [hiy, Equiv.swap_apply_right, e1]
        exact h1
      · have e1 : (if i = x then (1 : ZMod 2) else 0) + (if i = y then 1 else 0) = 0 := by
          simp [hix, hiy]
        rw [Equiv.swap_apply_of_ne_of_ne hix hiy, e1]
        exact CharTwo.add_self_eq_zero _

theorem s135_quad_closure {V : Type*} [CommGroup V] {S₀ : Set (MulAut V)}
    (hgen : ∀ s ∈ S₀, ∀ v : V, s v * v⁻¹ ∈ fixV (Subgroup.closure S₀)) :
    ∀ g ∈ Subgroup.closure S₀, ∀ v : V, g v * v⁻¹ ∈ fixV (Subgroup.closure S₀) := by
  classical
  set F := fixV (Subgroup.closure S₀) with hF
  have hfix : ∀ g ∈ Subgroup.closure S₀, ∀ x ∈ F, g x = x := fun g hg x hx => hx g hg
  intro g hg
  induction hg using Subgroup.closure_induction with
  | mem s hs => exact hgen s hs
  | one =>
    intro v
    rw [MulAut.one_apply, mul_inv_cancel]
    exact F.one_mem
  | mul a b ha hb iha ihb =>
    intro v
    have h1 : (a * b) v * v⁻¹ = a (b v * v⁻¹) * (a v * v⁻¹) := by
      rw [MulAut.mul_apply, map_mul, map_inv, mul_assoc, inv_mul_cancel_left]
    rw [h1, hfix a ha _ (ihb v)]
    exact F.mul_mem (ihb v) (iha v)
  | inv a ha iha =>
    intro v
    have hu : a (a⁻¹ v) = v := by
      rw [← MulAut.mul_apply, mul_inv_cancel, MulAut.one_apply]
    have h2 := iha (a⁻¹ v)
    rw [hu] at h2
    have h3 := F.inv_mem h2
    rwa [mul_inv_rev, inv_inv] at h3

omit [CommGroup W] in
theorem s135_alt_quad {n : ℕ} {S : Set (Equiv.Perm (Fin n))} (hS : ∀ t ∈ S, t.IsSwap)
    (hc : ∀ t ∈ S, ∀ t' ∈ S, t * t' = t' * t) :
    ∀ π ∈ Subgroup.closure S, ∀ v : ↥(coreMod n),
      coreAct n π v * v⁻¹ ∈ fixV ((Subgroup.closure S).map (coreAct n)) := by
  classical
  have hmap : (Subgroup.closure S).map (coreAct n) = Subgroup.closure ((coreAct n) '' S) :=
    MonoidHom.map_closure _ _
  have hF : fixV ((Subgroup.closure S).map (coreAct n)) =
      fixV (Subgroup.closure ((coreAct n) '' S)) := congrArg fixV hmap
  have key := s135_quad_closure (S₀ := (coreAct n) '' S) ?_
  · intro π hπ v
    have h1 : coreAct n π ∈ Subgroup.closure ((coreAct n) '' S) :=
      (SetLike.ext_iff.mp hmap _).mp (Subgroup.mem_map_of_mem _ hπ)
    exact (SetLike.ext_iff.mp hF _).mpr (key (coreAct n π) h1 v)
  · rintro _ ⟨t, ht, rfl⟩ v
    obtain ⟨x, y, hxy, rfl⟩ := hS t ht
    have hx : (Equiv.swap x y) x ≠ x := by simpa using hxy.symm
    have hpv := pairVec_swap_mem_fixV hS hc ht hx
    have e : pairVec x ((Equiv.swap x y) x) = pairVec x y := by rw [Equiv.swap_apply_left]
    have hFF : ∀ z : ↥(coreMod n), (z = 1 ∨ z = pairVec x y) →
        z ∈ fixV ((Subgroup.closure S).map (coreAct n)) := by
      rintro z (rfl | rfl)
      · exact Subgroup.one_mem _
      · exact (congrArg (fun z => z ∈ fixV ((Subgroup.closure S).map (coreAct n))) e).mp hpv
    exact (SetLike.ext_iff.mp hF _).mp (hFF _ (s135_swap_comm hxy v))


theorem s135_alt_main {n : ℕ} (hn : Odd n) {E U Q : Subgroup (MulAut W)} (hUQ : U ≤ Q)
    (hQN : Q ≤ Subgroup.normalizer (E : Set (MulAut W))) (β : W →* ↥(coreMod n))
    (hβ : Function.Bijective β)
    (ψ : ↥(Subgroup.normalizer (E : Set (MulAut W))) →* Equiv.Perm (Fin n))
    (hψ : ∀ (x : ↥(Subgroup.normalizer (E : Set (MulAut W)))) (w : W),
      β ((x : MulAut W) w) = coreAct n (ψ x) (β w))
    (hψinj : Function.Injective ψ) {S : Set (Equiv.Perm (Fin n))} (hS : ∀ t ∈ S, t.IsSwap)
    (hc : ∀ t ∈ S, ∀ t' ∈ S, t * t' = t' * t)
    (hUS : (U.subgroupOf (Subgroup.normalizer (E : Set (MulAut W)))).map ψ = Subgroup.closure S)
    (hfixE : fixV E = ⊥) {g : MulAut W} (hgQ : g ∈ Q)
    (hgU : g ∈ Subgroup.normalizer (U : Set (MulAut W))) (hg1 : g ≠ 1) :
    ∃ w : W, g w * w⁻¹ ∈ fixV U ∧ g w * w⁻¹ ∉ fixV E := by
  classical
  have hUN : U ≤ Subgroup.normalizer (E : Set (MulAut W)) := hUQ.trans hQN
  have hgN : g ∈ Subgroup.normalizer (E : Set (MulAut W)) := hQN hgQ
  obtain ⟨w₀, hw₀⟩ : ∃ w₀ : W, g w₀ ≠ w₀ := by
    by_contra hcon
    push Not at hcon
    exact hg1 (MulEquiv.ext fun w => by rw [hcon w]; rfl)
  have hnotE : ∀ r : W, r ≠ 1 → r ∉ fixV E := fun r hr hmem => hr (by
    rw [hfixE] at hmem
    exact Subgroup.mem_bot.mp hmem)
  by_cases hα : ∃ w₁ ∈ fixV U, g w₁ ≠ w₁
  · obtain ⟨w₁, hw₁, hne⟩ := hα
    exact ⟨w₁, (fixV U).mul_mem (s135_apply_mem_fixV hgU hw₁) ((fixV U).inv_mem hw₁),
      hnotE _ fun h => hne (mul_inv_eq_one.mp h)⟩
  push Not at hα
  have hψU : ∀ u (hu : u ∈ U), ψ ⟨u, hUN hu⟩ ∈ Subgroup.closure S := by
    intro u hu
    rw [← hUS]
    exact ⟨⟨u, hUN hu⟩, Subgroup.mem_subgroupOf.mpr hu, rfl⟩
  have hπ : ψ ⟨g, hgN⟩ ∈ Subgroup.closure S := by
    apply mem_closure_of_fixes hn hS hc
    intro v hv
    obtain ⟨w, rfl⟩ := hβ.2 v
    have hwU : w ∈ fixV U := by
      intro u hu
      have h1 : coreAct n (ψ ⟨u, hUN hu⟩) (β w) = β w :=
        hv _ (Subgroup.mem_map_of_mem _ (hψU u hu))
      apply hβ.1
      rw [hψ ⟨u, hUN hu⟩ w]
      exact h1
    rw [← hψ ⟨g, hgN⟩ w, hα w hwU]
  have hgU' : g ∈ U := by
    rw [← hUS] at hπ
    obtain ⟨x, hx, hxg⟩ := hπ
    have : x = ⟨g, hgN⟩ := hψinj hxg
    rw [this] at hx
    exact Subgroup.mem_subgroupOf.mp hx
  refine ⟨w₀, ?_, hnotE _ fun h => hw₀ (mul_inv_eq_one.mp h)⟩
  intro u hu
  apply hβ.1
  have hq := s135_alt_quad hS hc (ψ ⟨g, hgN⟩) hπ (β w₀)
  have h1 : coreAct n (ψ ⟨u, hUN hu⟩) (coreAct n (ψ ⟨g, hgN⟩) (β w₀) * (β w₀)⁻¹) =
      coreAct n (ψ ⟨g, hgN⟩) (β w₀) * (β w₀)⁻¹ :=
    hq _ (Subgroup.mem_map_of_mem _ (hψU u hu))
  have e1 : β ((u : MulAut W) (g w₀ * w₀⁻¹)) =
      coreAct n (ψ ⟨u, hUN hu⟩) (β (g w₀ * w₀⁻¹)) := hψ ⟨u, hUN hu⟩ _
  have e2 : β (g w₀) = coreAct n (ψ ⟨g, hgN⟩) (β w₀) := hψ ⟨g, hgN⟩ w₀
  rw [e1, map_mul, map_inv, e2]
  exact h1

end Alt

end Module

section Wrapper

variable {Γ : Type} [Group Γ] [Finite Γ] {G T E : Subgroup Γ}


omit [Group Γ] [Finite Γ] in
theorem s135_card_coreMod_three : Nat.card (coreMod 3) = 4 := by
  show Nat.card {x : PermMod 3 // ∑ i, Multiplicative.toAdd x i = 0} = 4
  rw [Nat.card_eq_fintype_card]
  decide +kernel

omit [Finite Γ] in
theorem s135_mem_fixOn_iff {W X : Subgroup Γ} (hWe : IsElemAbelian 2 W)
    (hX : X ≤ Subgroup.normalizer (W : Set Γ)) (r : ↥W) :
    r ∈ fixOn hWe X ↔ (r : Γ) ∈ Subgroup.centralizer (X : Set Γ) := by
  rw [fixOn_eq hWe hX, Subgroup.mem_subgroupOf]

omit [Finite Γ] in
theorem s135_coe_conjAct {W : Subgroup Γ} {y : Γ} (hy : y ∈ Subgroup.normalizer (W : Set Γ))
    (w : ↥W) : ((conjAct W ⟨y, hy⟩ w : ↥W) : Γ) = y * w * y⁻¹ :=
  conjAct_apply' W ⟨y, hy⟩ w

theorem s135_exists_commutator (hG : CharTwo G) (hT : IsSylowOf 2 T G) (hE : IsBTBlock G T E)
    {y : Γ} (hyT : y ∈ T) (hyE : y ∈ Subgroup.normalizer (E : Set Γ))
    (hnt : ∃ w ∈ pCoreOf 2 E, y * w * y⁻¹ ≠ w) :
    ∃ w ∈ pCoreOf 2 E, ⁅y, w⁆ ∈ Subgroup.centralizer (baum T : Set Γ) ∧
      ⁅y, w⁆ ∉ Subgroup.centralizer (E : Set Γ) := by
  classical
  set W : Subgroup Γ := pCoreOf 2 E with hWdef
  have hWe : IsElemAbelian 2 W := isElemAbelian_of_forall' hE.elemAbelian.1 hE.elemAbelian.2
  let _ : CommGroup ↥W := commGroupOfElemAbelian hWe
  have hEW : E ≤ Subgroup.normalizer (W : Set Γ) := le_normalizer_pCoreOf_self E
  have hperf : ⁅E, W⁆ = W := by rw [Subgroup.commutator_comm]; exact hE.perfect
  have hchar := charTwo_of_isBTBlock hG hT hE
  have hT2 : IsPGroup 2 ↥T := hT.2.1
  have hBN : baum T ≤ Subgroup.normalizer (E : Set Γ) := baum_le_normalizer_of_isBTBlock hE
  have hBT : baum T ≤ T := inf_le_left
  have hTB : T ≤ Subgroup.normalizer (baum T : Set Γ) :=
    Subgroup.le_normalizer.trans (normalizer_le_normalizer_baum T)
  have hB2 : IsPGroup 2 ↥(baum T) := hT2.to_le hBT
  have hJB : thompsonJ T ≤ baum T := B6.thompsonJ_le_baum T
  have hNW : Subgroup.normalizer (E : Set Γ) ≤ Subgroup.normalizer (W : Set Γ) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 E
  have hBW : baum T ≤ Subgroup.normalizer (W : Set Γ) := hBN.trans hNW
  set T₁ : Subgroup Γ := T ⊓ Subgroup.normalizer (E : Set Γ) with hT₁
  have hT₁W : T₁ ≤ Subgroup.normalizer (W : Set Γ) := inf_le_right.trans hNW
  have hT₁E : T₁ ≤ Subgroup.normalizer (E : Set Γ) := inf_le_right
  have hT₁B : T₁ ≤ Subgroup.normalizer (baum T : Set Γ) := inf_le_left.trans hTB
  have hQ : IsPGroup 2 ↥(autOn T₁ W) := isPGroup_autOn (hT2.to_le inf_le_left) hT₁W
  have hBT₁ : baum T ≤ T₁ := le_inf hBT hBN
  have hUQ : autOn (baum T) W ≤ autOn T₁ W := autOn_le_autOn W hBT₁
  have hQN : autOn T₁ W ≤ Subgroup.normalizer (autOn E W : Set (MulAut ↥W)) :=
    autOn_le_normalizer_autOn hT₁W hT₁E
  have hQB : autOn T₁ W ≤ Subgroup.normalizer (autOn (baum T) W : Set (MulAut ↥W)) :=
    autOn_le_normalizer_autOn hT₁W hT₁B
  have hyW : y ∈ Subgroup.normalizer (W : Set Γ) := hNW hyE
  set g : MulAut ↥W := conjAct W ⟨y, hyW⟩ with hg
  have hgQ : g ∈ autOn T₁ W := mem_autOn_iff.mpr ⟨⟨y, hyW⟩, ⟨hyT, hyE⟩, rfl⟩
  have hgU : g ∈ Subgroup.normalizer (autOn (baum T) W : Set (MulAut ↥W)) := hQB hgQ
  have hg1 : g ≠ 1 := by
    intro h1
    obtain ⟨w, hw, hne⟩ := hnt
    apply hne
    have := congrArg (fun φ : MulAut ↥W => ((φ ⟨w, hw⟩ : ↥W) : Γ)) h1
    simpa [hg, s135_coe_conjAct hyW] using this
  have key : ∃ w : ↥W, g w * w⁻¹ ∈ fixOn hWe (baum T) ∧ g w * w⁻¹ ∉ fixOn hWe E := by
    show ∃ w : ↥W, g w * w⁻¹ ∈ fixV (autOn (baum T) W) ∧ g w * w⁻¹ ∉ fixV (autOn E W)
    have h6 := six_four_d hG hT hE
    rw [blockW_eq_pCoreOf hE] at h6
    have hWT : W ≤ T := pCoreOf_le_sylow hG hT hE hT
    rcases hE.type with ⟨n, hn2, hn⟩ | ⟨m, hm, hn⟩
    ·
      have hbs := block_structure_sl hG hT hE hn2 hn
      rw [blockW_eq_pCoreOf hE] at hbs
      obtain ⟨hBE, hBcard, hJU⟩ := hbs
      have hnat : IsNatSL E W n := by
        have := isNatSL_of_isBTBlock hG hT hE hn
        rwa [blockW_eq_pCoreOf hE] at this
      obtain ⟨D⟩ := nonempty_slNatData hWe hEW hperf hnat
      have hFcard : Nat.card (GaloisField 2 n) = 2 ^ n := GaloisField.card 2 n (by omega)
      have hF : 2 ≤ Nat.card (GaloisField 2 n) := by
        rw [hFcard]
        exact Nat.le_self_pow (by omega) 2
      obtain ⟨A₀, hA₀, hA₀c⟩ :
          ∃ A, IsMaxElemAbelian T A ∧ ¬ A ≤ Subgroup.centralizer (W : Set Γ) := by
        by_contra hcon
        apply h6
        have hAc : ∀ A, IsMaxElemAbelian T A → A ≤ Subgroup.centralizer (W : Set Γ) :=
          fun A hA => by
            by_contra hA'
            exact hcon ⟨A, hA, hA'⟩
        have hJC : thompsonJ T ≤ Subgroup.centralizer (W : Set Γ) :=
          iSup_le fun A => iSup_le fun hA => hAc A hA
        rw [eq_bot_iff, Subgroup.commutator_le]
        intro w hw j hj
        rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
        exact Subgroup.mem_centralizer_iff.mp (hJC hj) w hw
      have hAJ : A₀ ≤ thompsonJ T := B6.le_thompsonJ hA₀
      have hAN : A₀ ≤ Subgroup.normalizer (W : Set Γ) := hAJ.trans (hJB.trans hBW)
      have hA₀E' : autOn A₀ W ≤ Subgroup.normalizer (autOn E W : Set (MulAut ↥W)) :=
        autOn_le_normalizer_autOn hAN ((hAJ.trans hJB).trans hBN)
      have hA₀w : Nat.card W ≤ Nat.card (autOn A₀ W) * Nat.card (fixV (autOn A₀ W)) := by
        rw [card_autOn_eq_relIndex hAN, card_fixV_autOn_eq hWe hAN]
        exact card_le_relIndex_mul_card_of_isMaxElemAbelian hA₀ hWe hWT hAN
      obtain ⟨-, hU₀card, hU₀q, hU₀W⟩ := sl_core_of_ne_bot D hA₀E'
        (isElemAbelian2_autOn hWe hA₀.2.1 hAN) (autOn_ne_bot_of_not_le_centralizer hAN hA₀c) hA₀w
      have hU₀le : autOn A₀ W ≤ autOn (baum T) W := (autOn_le_autOn W hAJ).trans hJU.le
      have hUeq : autOn A₀ W = autOn (baum T) W :=
        Subgroup.eq_of_le_of_card_ge hU₀le (by rw [hBcard, hU₀card, hFcard])
      have hUne : autOn (baum T) W ≠ ⊥ := hUeq ▸ autOn_ne_bot_of_not_le_centralizer hAN hA₀c
      rw [hUeq] at hU₀card hU₀q hU₀W
      exact s135_sl_main D hF hBE hUne hU₀card hU₀W hU₀q hQ hUQ hQN hgQ hgU hg1
    · by_cases hm2 : 2 ≤ m
      ·
        obtain ⟨D, ψ, hψ, hβbij, hψbij, -, -, k, hk1, hk2, hswap, -, -⟩ :=
          block_structure_alt hG hT hE hm2 hn hWdef hWe
        obtain ⟨S, hS, hc, -, hUS⟩ := hswap
        have hodd : Odd (2 * m + 1) := ⟨m, rfl⟩
        have hfixE : fixV (autOn E W) = ⊥ := by
          rw [eq_bot_iff]
          intro w hw
          rw [Subgroup.mem_bot]
          apply hβbij.1
          rw [map_one]
          exact (D.ker_iff hodd (by omega) w).mpr hw
        exact s135_alt_main hodd hUQ hQN D.β hβbij ψ hψ hψbij.1 hS hc hUS hfixE hgQ hgU hg1
      ·
        have hm1 : m = 1 := by omega
        subst hm1
        have hnat : IsNatAlt E W (2 * 1 + 1) := by
          have := isNatAlt_of_isBTBlock hG hT hE hn
          rwa [blockW_eq_pCoreOf hE] at this
        obtain ⟨D⟩ := nonempty_altNatData hWe hEW hperf hnat
        have hV2 : ∀ v : ↥W, v ^ 2 = 1 := fun v => Subtype.ext (by simpa [sq] using hWe.2 v v.2)
        have hfixE : fixV (autOn E W) = ⊥ := by
          have hcard : Nat.card ↥(autOn E W) = 3 := by
            rw [Nat.card_congr D.θ.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
            simp [Nat.factorial]
          have hodd : Odd (Nat.card ↥(autOn E W)) := by rw [hcard]; decide
          have h := (isCompl_fixV_commV_of_odd (autOn E W) hodd hV2).inf_eq_bot
          rwa [D.comm_top, inf_top_eq] at h
        have hβinj : Function.Injective D.β := by
          rw [injective_iff_map_eq_one]
          intro w hw
          have := (D.ker_iff (by decide) (by omega) w).mp hw
          rw [hfixE, Subgroup.mem_bot] at this
          exact this
        have hcardW : Nat.card W = 4 := by
          rw [Nat.card_congr (Equiv.ofBijective D.β ⟨hβinj, D.surj⟩)]
          exact s135_card_coreMod_three
        have hAN : baum T ≤ Subgroup.normalizer (W : Set Γ) := hBW
        have hUne : autOn (baum T) W ≠ ⊥ := by
          refine autOn_ne_bot_of_not_le_centralizer hAN fun hcen => h6 ?_
          rw [eq_bot_iff, Subgroup.commutator_le]
          intro w hw j hj
          rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
          exact Subgroup.mem_centralizer_iff.mp (hcen (hJB hj)) w hw
        have hW2 : IsPGroup 2 ↥W := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 E
        obtain ⟨w, hwW, hw1, hwfix⟩ := exists_ne_one_fixed_of_isPGroup hW2
          (pCoreOf_ne_bot hE hchar) hB2 hBW
        have hfixU : ∃ w : ↥W, w ∈ fixV (autOn (baum T) W) ∧ w ≠ 1 := by
          refine ⟨⟨w, hwW⟩, ?_, fun h => hw1 (congrArg Subtype.val h)⟩
          refine (s135_mem_fixOn_iff hWe hBW ⟨w, hwW⟩).mpr ?_
          rw [Subgroup.mem_centralizer_iff]
          intro p hp
          have := hwfix p hp
          calc p * w = (p * w * p⁻¹) * p := by group
            _ = w * p := by rw [this]
        exact s135_a3_main hcardW hfixE hUne hfixU hgU hg1
  obtain ⟨w, hw1, hw2⟩ := key
  refine ⟨(w : Γ), w.2, ?_, ?_⟩
  · have := (s135_mem_fixOn_iff hWe hBW _).mp hw1
    have e : (((g w * w⁻¹ : ↥W)) : Γ) = ⁅y, (w : Γ)⁆ := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, hg, s135_coe_conjAct hyW]
      rfl
    rwa [e] at this
  · intro hc
    apply hw2
    refine (s135_mem_fixOn_iff hWe hEW _).mpr ?_
    have e : (((g w * w⁻¹ : ↥W)) : Γ) = ⁅y, (w : Γ)⁆ := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, hg, s135_coe_conjAct hyW]
      rfl
    rwa [e]

end Wrapper

end CFSG.CGT.PushingUpLit.BHS7
