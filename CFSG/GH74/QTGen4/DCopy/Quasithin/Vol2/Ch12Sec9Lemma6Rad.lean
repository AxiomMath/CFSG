module

public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma6Rad
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec8OneFlag
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec9Lemma9W0

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint
open scoped IsMulCommutative commutatorElement

namespace L1296

variable {G : Type} [Group G]

variable [CFSG.GH74.QTGen4.Finite4 G]

theorem le_of_tinv_of_lOne_F4 (h1222 : Stmt12_2_2_F4) {T L V : Subgroup G} {n : ℕ}
    (h : Hyp1281One G T L V n) {V₁ W : Subgroup G} (hV₁ : IsTSub T V V₁ 1) (hWV : W ≤ V)
    (hTW : T ≤ Subgroup.normalizer (W : Set G))
    (hLW : lOne L V₁ ≤ Subgroup.normalizer (W : Set G)) (hne : W ≠ V) : W ≤ V₁ := by
  rcases tinv_comparable_of_hyp1281One_F4 h1222 h hWV hV₁.1 hTW hV₁.2.2 with hle | hle
  · exact hle
  · rcases eq_or_eq_of_lOne_le_normalizer h hV₁ hle hWV hLW with heq | heq
    · exact heq.le
    · exact absurd heq hne

theorem le_centralizer_of_le_T_F4 (h1222 : Stmt12_2_2_F4) {T L V : Subgroup G} {n : ℕ}
    (h : Hyp1281One G T L V n) {V₁ Y : Subgroup G} (hV₁ : IsTSub T V V₁ 1) (hYT : Y ≤ T)
    (hTY : T ≤ Subgroup.normalizer (Y : Set G))
    (hLY : lOne L V₁ ≤ Subgroup.normalizer (Y : Set G))
    (hLYc : ∀ l ∈ lOne L V₁, ∀ y ∈ Y, l * y * l⁻¹ * y⁻¹ ∈ Subgroup.centralizer (V : Set G)) :
    Y ≤ Subgroup.centralizer (V : Set G) := by
  obtain ⟨hVT, hTV⟩ := h.hyp.le_and_normalizes_F4 h1222
  have hW : ⁅V, Y⁆ ≤ V₁ :=
    le_of_tinv_of_lOne_F4 h1222 h hV₁ (Subgroup.le_normalizer_iff_commutator_le_left.1
      (hYT.trans hTV)) (le_normalizer_commutator hTV hTY)
      (le_normalizer_commutator (lOne_le_normalizer h V₁) hLY)
      (commutator_lt h.hyp.sylow.1 hVT hYT hTV h.hyp.irrPlus.2.1).ne
  refine L1299.le_centralizer_of_commutator_le_lOne h hV₁ (hYT.trans hV₁.2.2)
    (fun v hv y hy => ?_) hLYc
  have h1 := V₁.inv_mem (hW (Subgroup.commutator_mem_commutator hv hy))
  rwa [commutatorElement_def, show (v * y * v⁻¹ * y⁻¹)⁻¹ = y * v * y⁻¹ * v⁻¹ by group] at h1

theorem commutator_pCoreOf_le_F4 (h1222 : Stmt12_2_2_F4) {T L V : Subgroup G} {n : ℕ}
    (h : Hyp1281One G T L V n) {V₁ : Subgroup G} (hV₁ : IsTSub T V V₁ 1) :
    ⁅V, pCoreOf 2 (lOne L V₁ ⊔ T)⁆ ≤ V₁ := by
  obtain ⟨hVT, hTV⟩ := h.hyp.le_and_normalizes_F4 h1222
  have hRT := pCoreOf_le_T h V₁
  have hN := LieType.BorelTits.le_normalizer_pCoreOf 2 (lOne L V₁ ⊔ T)
  exact le_of_tinv_of_lOne_F4 h1222 h hV₁
    (Subgroup.le_normalizer_iff_commutator_le_left.1 (hRT.trans hTV))
    (le_normalizer_commutator hTV (le_sup_right.trans hN))
    (le_normalizer_commutator (lOne_le_normalizer h V₁) (le_sup_left.trans hN))
    (commutator_lt h.hyp.sylow.1 hVT hRT hTV h.hyp.irrPlus.2.1).ne

theorem inf_centralizer_le_pCoreOf_F4 (h1222 : Stmt12_2_2_F4) {T L V : Subgroup G} {n : ℕ}
    (h : Hyp1281One G T L V n) (V₁ : Subgroup G) :
    T ⊓ Subgroup.centralizer (V : Set G) ≤ pCoreOf 2 (lOne L V₁ ⊔ T) := by
  have hN := (inf_centralizer_eq_sup_inf_centralizer_F4 h1222 h).2
  have hL₁L : lOne L V₁ ≤ L := (oTwoUpper_le _).trans inf_le_left
  exact LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (inf_le_left.trans le_sup_right)
    ((sup_le_sup_right hL₁L T).trans hN) (h.hyp.sylow.1.to_le inf_le_left)

theorem card_pCoreOf_le_F4 (h1222 : Stmt12_2_2_F4) {T L V : Subgroup G} {n : ℕ}
    (h : Hyp1281One G T L V n) {V₁ : Subgroup G} (hV₁ : IsTSub T V V₁ 1) :
    Nat.card ↥(pCoreOf 2 (lOne L V₁ ⊔ T)) ≤
      2 ^ (n - 1) * Nat.card ↥(T ⊓ Subgroup.centralizer (V : Set G)) := by
  obtain ⟨hcard, hsq, hab⟩ := h.card_sq
  obtain ⟨-, hTV⟩ := h.hyp.le_and_normalizes_F4 h1222
  have hRT := pCoreOf_le_T h V₁
  have hV₁2 : Nat.card V₁ = 2 := by simpa using hV₁.2.1
  have hc := commutator_pCoreOf_le_F4 h1222 h hV₁
  have h1 := card_le_of_commutator_mem hab hsq hcard hV₁.1 hV₁2 (hRT.trans hTV)
    (fun r hr v hv => by
      have h2 := V₁.inv_mem (hc (Subgroup.commutator_mem_commutator hv hr))
      rwa [commutatorElement_def, show (v * r * v⁻¹ * r⁻¹)⁻¹ = r * v * r⁻¹ * v⁻¹ by group] at h2)
    (fun r hr x hx => by
      have h2 := Subgroup.mem_centralizer_iff.1
        (le_centralizer_normalizer_of_card_eq_two hV₁2 hx) r (hV₁.2.2 (hRT hr))
      rw [h2, mul_inv_cancel_right])
  exact h1.trans (Nat.mul_le_mul_left _ (Subgroup.card_le_of_le (inf_le_inf_right _ hRT)))

theorem inf_centralizer_lt_pCoreOf_F4 (h1222 : Stmt12_2_2_F4) {T L V : Subgroup G} {n : ℕ}
    (h : Hyp1281One G T L V n) {V₁ : Subgroup G} (hV₁ : IsTSub T V V₁ 1) :
    T ⊓ Subgroup.centralizer (V : Set G) < pCoreOf 2 (lOne L V₁ ⊔ T) := by
  classical
  obtain ⟨hcard, hsq, hab⟩ := h.card_sq
  obtain ⟨hc, -⟩ := h.natural
  obtain ⟨hVT, hTV⟩ := h.hyp.le_and_normalizes_F4 h1222
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := h.hyp.irrPlus.2.2.1
  have hT2 : IsPGroup 2 T := h.hyp.sylow.1
  have hV₁2 : Nat.card V₁ = 2 := by simpa using hV₁.2.1
  have hn2 : 2 ≤ n := by rcases h.n_mem with rfl | rfl | rfl <;> omega
  obtain ⟨V₂, hV₂, hV₁₂⟩ := exists_tsub_two_of_one hT2 hsq hab hTV hcard hn2 hV₁
  obtain ⟨v₁, hv₁, hv₁1⟩ : ∃ v ∈ V₁, v ≠ 1 := by
    by_contra hne
    push Not at hne
    have hbot : V₁ = ⊥ := (Subgroup.eq_bot_iff_forall _).2 hne
    rw [hbot, Subgroup.card_bot] at hV₁2
    norm_num at hV₁2
  obtain ⟨v₂, hv₂, hv₂1⟩ : ∃ v ∈ V₂, v ∉ V₁ := by
    by_contra hne
    push Not at hne
    have h1 := Subgroup.card_le_of_le (show V₂ ≤ V₁ from hne)
    rw [hV₂.2.1, hV₁.2.1] at h1
    norm_num at h1
  have hv₁V := hV₁.1 hv₁
  have hv₂V := hV₂.1 hv₂
  let _ := zmodModuleOf hsq
  set a₁ : Additive ↥V := Additive.ofMul ⟨v₁, hv₁V⟩ with ha₁
  set a₂ : Additive ↥V := Additive.ofMul ⟨v₂, hv₂V⟩ with ha₂
  have ha : a₂ ∉ (ZMod 2) ∙ a₁ := by
    intro hmem
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hmem
    rcases zmod_two_cases c with rfl | rfl
    · rw [zero_smul] at hc
      apply hv₂1
      have := congrArg (fun x : Additive ↥V => ((Additive.toMul x : ↥V) : G)) hc
      simp only [ha₂, toMul_ofMul, toMul_zero, OneMemClass.coe_one] at this
      rw [← this]
      exact V₁.one_mem
    · rw [one_smul] at hc
      apply hv₂1
      have := congrArg (fun x : Additive ↥V => ((Additive.toMul x : ↥V) : G)) hc
      simp only [ha₁, ha₂, toMul_ofMul] at this
      rw [← this]
      exact hv₁
  obtain ⟨f, hf1, hf2⟩ := Submodule.exists_le_ker_of_notMem ha
  have hfa₁ : f a₁ = 0 := LinearMap.mem_ker.1 (hf2 (Submodule.mem_span_singleton_self a₁))
  have hfa₂ : f a₂ = 1 := Flag.zmod_two_eq_one hf1
  let τ0 : Additive ↥V →ₗ[ZMod 2] Additive ↥V := LinearMap.id + f.smulRight a₁
  have hτ0 : ∀ x, τ0 x = x + f x • a₁ := fun x => rfl
  have hinv : Function.Involutive τ0 := by
    intro x
    rw [hτ0, hτ0, map_add, map_smul, hfa₁, smul_zero, add_zero, add_assoc, ← add_smul,
      CharTwo.add_self_eq_zero, zero_smul, add_zero]
  let α : MulAut ↥V :=
    { toFun := fun x => Additive.toMul (τ0 (Additive.ofMul x))
      invFun := fun x => Additive.toMul (τ0 (Additive.ofMul x))
      left_inv := fun x => by
        simp only [ofMul_toMul]
        rw [hinv]
        rfl
      right_inv := fun x => by
        simp only [ofMul_toMul]
        rw [hinv]
        rfl
      map_mul' := fun x y => by simp only [ofMul_mul, map_add, toMul_add] }
  have hα : ∀ x : ↥V, ((α x : ↥V) : G) = (x : G) ∨ ((α x : ↥V) : G) = (x : G) * v₁ := by
    intro x
    have e : α x = x * Additive.toMul (f (Additive.ofMul x) • a₁) := by
      show Additive.toMul (τ0 (Additive.ofMul x)) = _
      rw [hτ0, toMul_add, toMul_ofMul]
    rcases zmod_two_cases (f (Additive.ofMul x)) with h0 | h1
    · left
      rw [e, h0, zero_smul, toMul_zero, mul_one]
    · right
      rw [e, h1, one_smul, Subgroup.coe_mul, ha₁, toMul_ofMul]
  have hα₂ : ((α ⟨v₂, hv₂V⟩ : ↥V) : G) = v₂ * v₁ := by
    show ((Additive.toMul (τ0 a₂) : ↥V) : G) = _
    rw [hτ0, hfa₂, one_smul, toMul_add, Subgroup.coe_mul, ha₁, ha₂, toMul_ofMul, toMul_ofMul]

  have hαL : α ∈ autOn L V := by
    rw [autOn_eq_top_of_hyp1281One h]
    exact Subgroup.mem_top _
  obtain ⟨⟨g, hgN⟩, hgL, hgα⟩ := hαL
  simp only [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hgL
  have hconj : ∀ x (hx : x ∈ V), g * x * g⁻¹ = ((α ⟨x, hx⟩ : ↥V) : G) := by
    intro x hx
    rw [← hgα]
    rfl

  have hgV₁ : ∀ x ∈ V₁, g * x * g⁻¹ = x := by
    intro x hx
    by_cases hx1 : x = 1
    · rw [hx1]
      group
    have e := SteinbergBS.eq_of_card_le_two hV₁2.le hx hv₁ hx1 hv₁1
    subst e
    rw [hconj x hv₁V]
    show ((Additive.toMul (τ0 a₁) : ↥V) : G) = x
    rw [hτ0, hfa₁, zero_smul, add_zero, ha₁, toMul_ofMul]
  have hgN₁ : g ∈ Subgroup.normalizer (V₁ : Set G) :=
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.2 fun x hx => by
      have := hgV₁ x hx
      calc x * g = g * x * g⁻¹ * g := by rw [this]
        _ = g * x := by group)

  set E := centralizerMod V₁ (L ⊔ T) V with hEdef
  have hgE : g ∈ E := by
    refine ⟨Subgroup.mem_sup_left hgL, hgN₁, fun u hu => ?_⟩
    rw [hconj u hu]
    rcases hα ⟨u, hu⟩ with e | e
    · rw [e, mul_inv_cancel]
      exact V₁.one_mem
    · rw [e, show u * v₁ * u⁻¹ = v₁ from by
        rw [hab u hu v₁ hv₁V]; group]
      exact hv₁
  have hQ := (inf_centralizer_eq_sup_inf_centralizer_F4 h1222 h).1
  have hEp : IsPGroup 2 E := by
    intro x
    obtain ⟨hxX, hxN, hxc⟩ := x.2
    have hx2 : (x : G) * (x : G) ∈ T ⊓ Subgroup.centralizer (V : Set G) := by
      rw [hQ]
      refine ⟨Subgroup.mul_mem _ hxX hxX, Subgroup.mem_centralizer_iff.2 fun u hu => ?_⟩
      set c := (x : G) * u * (x : G)⁻¹ * u⁻¹ with hcdef
      have hd : c ∈ V₁ := hxc u hu
      have hxc' : (x : G) * c * (x : G)⁻¹ = c := by
        have h1 := Subgroup.mem_centralizer_iff.1
          (le_centralizer_normalizer_of_card_eq_two hV₁2 hd) _ hxN
        rw [h1, mul_inv_cancel_right]
      have hcc : c * c = 1 := by rw [← sq]; exact hsq _ (hV₁.1 hd)
      have hxu : (x : G) * u * (x : G)⁻¹ = c * u := by rw [hcdef]; group
      have key : (x : G) * (x : G) * u * ((x : G) * (x : G))⁻¹ = u := by
        calc (x : G) * (x : G) * u * ((x : G) * (x : G))⁻¹ =
              (x : G) * ((x : G) * u * (x : G)⁻¹) * (x : G)⁻¹ := by group
          _ = (x : G) * (c * u) * (x : G)⁻¹ := by rw [hxu]
          _ = ((x : G) * c * (x : G)⁻¹) * ((x : G) * u * (x : G)⁻¹) := by group
          _ = c * (c * u) := by rw [hxc', hxu]
          _ = u := by rw [← mul_assoc, hcc, one_mul]
      calc u * ((x : G) * (x : G)) =
            ((x : G) * (x : G) * u * ((x : G) * (x : G))⁻¹) * ((x : G) * (x : G)) := by
            rw [key]
        _ = (x : G) * (x : G) * u := by group
    obtain ⟨k, hk⟩ := (hT2.to_le inf_le_left) ⟨_, hx2⟩
    refine ⟨k + 1, Subtype.ext ?_⟩
    have h1 := congrArg Subtype.val hk
    simp only [Subgroup.coe_pow, Subgroup.coe_one] at h1 ⊢
    rw [pow_succ', pow_mul, sq]
    exact h1
  have hTE : T ≤ Subgroup.normalizer (E : Set G) :=
    le_normalizer_centralizerMod (le_sup_right.trans Subgroup.le_normalizer) hV₁.2.2 hTV
  have hET : E ≤ T := le_of_isPGroup h.hyp.sylow hEp hTE

  have hL₁E : lOne L V₁ ⊔ T ≤ Subgroup.normalizer (E : Set G) := by
    refine sup_le (le_normalizer_centralizerMod ?_ ?_ (lOne_le_normalizer h V₁)) hTE
    · exact ((oTwoUpper_le _).trans (inf_le_left.trans le_sup_left)).trans Subgroup.le_normalizer
    · exact (oTwoUpper_le _).trans inf_le_right
  have hER : E ≤ pCoreOf 2 (lOne L V₁ ⊔ T) :=
    LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (hET.trans le_sup_right) hL₁E hEp
  refine lt_of_le_of_ne (inf_centralizer_le_pCoreOf_F4 h1222 h V₁) fun heq => ?_
  have hgQ : g ∈ T ⊓ Subgroup.centralizer (V : Set G) := by
    rw [heq]
    exact hER hgE
  have h1 := Subgroup.mem_centralizer_iff.1 hgQ.2 v₂ hv₂V
  have h2 : g * v₂ * g⁻¹ = v₂ := by rw [← h1]; group
  rw [hconj v₂ hv₂V, hα₂] at h2
  apply hv₁1
  calc v₁ = v₂⁻¹ * (v₂ * v₁) := by group
    _ = 1 := by rw [h2, inv_mul_cancel]

end L1296

end CFSG.Quasithin.H13
