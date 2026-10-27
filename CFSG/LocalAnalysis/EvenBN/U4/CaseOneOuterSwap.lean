module

public import CFSG.LocalAnalysis.EvenBN.U4.CaseOneOuterCosets
public import CFSG.LocalAnalysis.EvenBN.U4.Prelim.FieldFromTransitive

public section

namespace CFSG.LocalAnalysis.EvenBN.U4

open Subgroup CFSG.Open CFSG.LocalAnalysis CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.LocalAnalysis.EvenBN.Common (prodFactorOne prodFactorTwo card_sup_mul_card_inf_eq
  mem_normalizer_inf mem_normalizer_sup)
open scoped MatrixGroups

theorem mem_of_commute_of_transitive {V : Type*} [Group V] {J : Subgroup (MulAut V)}
    (hJ : ∀ a ∈ J, ∀ b ∈ J, a * b = b * a)
    (htrans : ∀ v w : V, v ≠ 1 → w ≠ 1 → ∃ a ∈ J, a v = w) {g : MulAut V}
    (hg : ∀ a ∈ J, g * a = a * g) : g ∈ J := by
  rcases subsingleton_or_nontrivial V with hV | hV
  · have : g = 1 := MulEquiv.ext fun v => Subsingleton.elim _ _
    rw [this]
    exact one_mem _
  obtain ⟨v₀, hv₀⟩ := exists_ne (1 : V)
  have hgv : g v₀ ≠ 1 := fun e => hv₀ (by rw [← map_one g] at e; exact g.injective e)
  obtain ⟨a, ha, hav⟩ := htrans v₀ (g v₀) hv₀ hgv
  have hb : a⁻¹ * g = 1 := by
    ext v
    rw [MulAut.one_apply]
    by_cases hv : v = 1
    · rw [hv, map_one]
    obtain ⟨c, hc, rfl⟩ := htrans v₀ v hv₀ hv
    have h1 : (a⁻¹ * g) * c = c * (a⁻¹ * g) := by
      rw [mul_assoc, hg c hc, ← mul_assoc, ← mul_assoc]
      congr 1
      have := hJ a ha c hc
      calc a⁻¹ * c = a⁻¹ * (c * a) * a⁻¹ := by group
        _ = a⁻¹ * (a * c) * a⁻¹ := by rw [this]
        _ = c * a⁻¹ := by group
    have h2 : (a⁻¹ * g) v₀ = v₀ := by
      rw [MulAut.mul_apply, ← hav, ← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply]
    rw [← MulAut.mul_apply, h1, MulAut.mul_apply, h2]
  rw [inv_mul_eq_one] at hb
  rw [← hb]
  exact ha

namespace Setting

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {L : Subgroup G} {η : L ≃* gramSU h (miyamotoJ4 K)} {t : G}
  {Q T : Subgroup G}

local notation "𝓦" => miyamotoRG h L η t Q ⊓ centralizer (miyamotoI1G h L η : Set G)

variable {k : Type} [Field k] {ψ : miyamotoM1G h L η t ≃* SL(2, k) × SL(2, k)}

local notation "𝓤" => miyamotoF1G h L η t ⊔ (𝓦 ⊓ prodFactorOne ψ)

@[expose] noncomputable def prodSnd (ψ : miyamotoM1G h L η t ≃* SL(2, k) × SL(2, k)) :
    miyamotoM1G h L η t →* G :=
  (miyamotoM1G h L η t).subtype.comp (ψ.symm.toMonoidHom.comp
    ((MonoidHom.inr _ _).comp ((MonoidHom.snd _ _).comp ψ.toMonoidHom)))

@[expose] noncomputable def prodFst (ψ : miyamotoM1G h L η t ≃* SL(2, k) × SL(2, k)) :
    miyamotoM1G h L η t →* G :=
  (miyamotoM1G h L η t).subtype.comp (ψ.symm.toMonoidHom.comp
    ((MonoidHom.inl _ _).comp ((MonoidHom.fst _ _).comp ψ.toMonoidHom)))

omit [Finite G] in
theorem prodSnd_apply (x : miyamotoM1G h L η t) :
    prodSnd ψ x = ((ψ.symm (1, (ψ x).2) : miyamotoM1G h L η t) : G) := rfl

omit [Finite G] in
theorem prodFst_apply (x : miyamotoM1G h L η t) :
    prodFst ψ x = ((ψ.symm ((ψ x).1, 1) : miyamotoM1G h L η t) : G) := rfl

omit [Finite G] in
theorem prodSnd_mem (x : miyamotoM1G h L η t) : prodSnd ψ x ∈ prodFactorTwo ψ :=
  Common.symm_inr_mem_prodFactorTwo ψ _

omit [Finite G] in
theorem prodFst_mem (x : miyamotoM1G h L η t) : prodFst ψ x ∈ prodFactorOne ψ :=
  Common.symm_inl_mem_prodFactorOne ψ _

omit [Finite G] in
theorem eq_prodFst_mul_prodSnd (x : miyamotoM1G h L η t) :
    (x : G) = prodFst ψ x * prodSnd ψ x := by
  rw [prodFst_apply, prodSnd_apply, ← Subgroup.coe_mul, ← map_mul, Prod.mk_mul_mk, mul_one,
    one_mul, Prod.mk.eta, MulEquiv.symm_apply_apply]

omit [Finite G] in
theorem eq_of_mul_eq_mul_of_mem {a₁ a₂ b₁ b₂ : G} (ha₁ : a₁ ∈ prodFactorOne ψ)
    (ha₂ : a₂ ∈ prodFactorTwo ψ) (hb₁ : b₁ ∈ prodFactorOne ψ) (hb₂ : b₂ ∈ prodFactorTwo ψ)
    (e : a₁ * a₂ = b₁ * b₂) : a₁ = b₁ ∧ a₂ = b₂ := by
  have hm : b₁⁻¹ * a₁ ∈ prodFactorOne ψ ⊓ prodFactorTwo ψ := by
    refine mem_inf.2 ⟨mul_mem (inv_mem hb₁) ha₁, ?_⟩
    have : b₁⁻¹ * a₁ = b₂ * a₂⁻¹ := by
      calc b₁⁻¹ * a₁ = b₁⁻¹ * (a₁ * a₂) * a₂⁻¹ := by group
        _ = b₂ * a₂⁻¹ := by rw [e]; group
    rw [this]
    exact mul_mem hb₂ (inv_mem ha₂)
  rw [Common.prodFactorOne_inf_prodFactorTwo ψ, mem_bot] at hm
  have h1 : a₁ = b₁ := (eq_of_inv_mul_eq_one hm).symm
  refine ⟨h1, ?_⟩
  rw [h1] at e
  exact mul_left_cancel e

omit [Finite G] in
theorem conj_prodSnd {u : G} (hX1 : ∀ x ∈ prodFactorOne ψ, u * x * u⁻¹ ∈ prodFactorOne ψ)
    (hX2 : ∀ x ∈ prodFactorTwo ψ, u * x * u⁻¹ ∈ prodFactorTwo ψ) (x y : miyamotoM1G h L η t)
    (hxy : (y : G) = u * x * u⁻¹) : u * prodSnd ψ x * u⁻¹ = prodSnd ψ y := by
  have e : (u * prodFst ψ x * u⁻¹) * (u * prodSnd ψ x * u⁻¹) = prodFst ψ y * prodSnd ψ y := by
    rw [← eq_prodFst_mul_prodSnd (ψ := ψ) y, hxy, eq_prodFst_mul_prodSnd (ψ := ψ) x]
    group
  exact (eq_of_mul_eq_mul_of_mem (hX1 _ (prodFst_mem (ψ := ψ) x)) (hX2 _ (prodSnd_mem (ψ := ψ) x))
    (prodFst_mem (ψ := ψ) y) (prodSnd_mem (ψ := ψ) y) e).2


theorem mul_mem_centralizer_E [Fintype k] (hS : Setting h L η t Q T)
    (hk : Fintype.card k = (2 ^ f) ^ 2)
    (hψt : ∀ (x y : miyamotoM1G h L η t) (y₁ y₂ : SL(2, k)), (y : G) = t⁻¹ * x * t →
      ψ x = (y₁, y₂) → ψ y = (y₂, y₁))
    {α : miyamotoN1G h L η ≃* SL(2, k)}
    (hψα : ∀ (a : miyamotoN1G h L η) (x : miyamotoM1G h L η t), (x : G) = a →
      ψ x = (α a, α a))
    (hZ : Nat.card (CFSG.centerIn 𝓤) = (2 ^ f) ^ 4)
    {u : G} (huu : u * u = 1) (hut : u * t = t * u)
    (huE : u ∈ normalizer (miyamotoEG h L η Q : Set G))
    (hX1 : ∀ x ∈ prodFactorOne ψ, u * x * u⁻¹ ∈ prodFactorOne ψ)
    (hX2 : ∀ x ∈ prodFactorTwo ψ, u * x * u⁻¹ ∈ prodFactorTwo ψ)
    (hD : ∀ d ∈ miyamotoDG h L η, u * d * u⁻¹ = d ^ (2 ^ f)) :
    t * u ∈ centralizer (miyamotoEG h L η Q : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP k 2 := charP_of_card_eq_prime_pow (f := 2 * f) (by rw [hk, ← pow_mul, mul_comm])
  have hk' : Nat.card k = 2 ^ (2 * f) := by
    rw [Nat.card_eq_fintype_card, hk, ← pow_mul, mul_comm]
  have hDM : miyamotoDG h L η ≤ miyamotoM1G h L η t := hS.DG_le_N1G.trans hS.sec3_12_one.2.2.1
  set D' : Subgroup (miyamotoM1G h L η t) := (miyamotoDG h L η).subgroupOf (miyamotoM1G h L η t)
    with hD'
  set π : D' →* G := (prodSnd ψ).comp D'.subtype with hπ
  have hπinj : Function.Injective π := by
    rw [injective_iff_map_eq_one]
    rintro ⟨d, hd⟩ hd1
    have hdD : (d : G) ∈ miyamotoDG h L η := hd
    have hdN : (d : G) ∈ miyamotoN1G h L η := hS.DG_le_N1G hdD
    have e1 : ψ.symm (1, (ψ d).2) = 1 := Subtype.ext hd1
    have e2 : (ψ d).2 = 1 := by
      have := congrArg ψ e1
      rw [MulEquiv.apply_symm_apply, map_one] at this
      exact (Prod.mk.inj this).2
    rw [hψα ⟨d, hdN⟩ d rfl] at e2
    have e3 : (⟨d, hdN⟩ : miyamotoN1G h L η) = 1 := by
      rw [← map_one α] at e2
      exact α.injective e2
    have e4 : (d : G) = 1 := congrArg Subtype.val e3
    exact Subtype.ext (Subtype.ext e4)
  set T₂ : Subgroup G := π.range with hT₂
  have hT2card : Nat.card T₂ = (2 ^ f) ^ 2 - 1 := by
    rw [hT₂, Nat.card_congr (MonoidHom.ofInjective hπinj).toEquiv.symm, hD',
      Nat.card_congr (subgroupOfEquivOfLe hDM).toEquiv, card_miyamotoDG]
  have hT2X : T₂ ≤ prodFactorTwo ψ := by
    rintro _ ⟨d, rfl⟩
    exact prodSnd_mem _
  have hDc : ∀ a ∈ miyamotoDG h L η, ∀ b ∈ miyamotoDG h L η, a * b = b * a := by
    intro a ha b hb
    rw [← range_miyamotoDHom] at ha hb
    obtain ⟨α₁, rfl⟩ := ha
    obtain ⟨β₁, rfl⟩ := hb
    rw [← map_mul, ← map_mul, mul_comm]
  have hT2c : ∀ a ∈ T₂, ∀ b ∈ T₂, a * b = b * a := by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (Subtype.ext (hDc _ a.2 _ b.2))
  set W₂ := 𝓦 ⊓ prodFactorTwo ψ with hW₂
  have hT2N : T₂ ≤ normalizer ((W₂ : Subgroup G) : Set G) := by
    rintro _ ⟨⟨d, hd⟩, rfl⟩
    have hdD : (d : G) ∈ miyamotoDG h L η := hd
    have hdW : (d : G) ∈ normalizer ((W₂ : Subgroup G) : Set G) :=
      mem_normalizer_inf (hS.DG_le_normalizer_W hdD)
        (Common.le_normalizer_prodFactorTwo ψ d.2)
    have e : π ⟨d, hd⟩ = (prodFst ψ d)⁻¹ * d := by
      show prodSnd ψ d = _
      rw [eq_inv_mul_iff_mul_eq, ← eq_prodFst_mul_prodSnd]
    rw [e]
    refine mem_normalizer_fintype fun w hw => ?_
    have hdw : (d : G) * w * (d : G)⁻¹ ∈ W₂ := (mem_normalizer_iff.1 hdW w).1 hw
    have hc : prodFst ψ d * (d * w * (d : G)⁻¹) = (d * w * (d : G)⁻¹) * prodFst ψ d :=
      mem_centralizer_iff.1 (Common.prodFactorTwo_le_centralizer ψ (mem_inf.1 hdw).2) _
        (prodFst_mem d)
    show (prodFst ψ d)⁻¹ * d * w * ((prodFst ψ d)⁻¹ * d)⁻¹ ∈ W₂
    have : (prodFst ψ d)⁻¹ * d * w * ((prodFst ψ d)⁻¹ * d)⁻¹ = d * w * (d : G)⁻¹ := by
      calc (prodFst ψ d)⁻¹ * d * w * ((prodFst ψ d)⁻¹ * d)⁻¹ =
          (prodFst ψ d)⁻¹ * (d * w * (d : G)⁻¹) * prodFst ψ d := by group
        _ = (prodFst ψ d)⁻¹ * (prodFst ψ d * (d * w * (d : G)⁻¹)) := by rw [mul_assoc, hc]
        _ = d * w * (d : G)⁻¹ := by group
    rw [this]
    exact hdw
  have hW2card : Nat.card W₂ = (2 ^ f) ^ 2 := (hS.W_eq_sup (ψ := ψ) hk).2.2
  have hT2inf : T₂ ⊓ W₂ = ⊥ := by
    refine disjoint_iff.1 (Subgroup.disjoint_of_coprime_natCard ?_)
    rw [hT2card, hW2card]
    have hodd : Odd ((2 ^ f) ^ 2 - 1) := Nat.Even.sub_odd (Nat.one_le_pow _ _ (by positivity))
      ((Nat.even_pow.2 ⟨even_two, by have := hS.two_le; omega⟩).pow_of_ne_zero two_ne_zero)
      odd_one
    rw [show (2 ^ f) ^ 2 = 2 ^ (f * 2) by rw [← pow_mul]] at hodd ⊢
    exact Nat.Coprime.pow_right _ (Nat.coprime_two_right.2 hodd)
  have hZF1 : CFSG.centerIn 𝓤 ≤ miyamotoF1G h L η t := hS.centerIn_U_le_F1
  have hcommZ : ∀ a ∈ CFSG.centerIn 𝓤, ∀ b ∈ CFSG.centerIn 𝓤, a * b = b * a :=
    fun a ha b hb => hS.F1_comm (hZF1 ha) (hZF1 hb)
  have hXA : prodFactorTwo ψ ≤ normalizer ((CFSG.centerIn 𝓤 : Subgroup G) : Set G) :=
    fun x hx => normalizer_le_normalizer_centerIn _ (hS.X2_le_normalizer_U hx)
  have hcardZ : Nat.card (CFSG.centerIn 𝓤) = (2 ^ (2 * f)) ^ 2 := by
    rw [hZ, ← pow_mul, ← pow_mul]
    ring_nf
  have hfixZ : CFSG.centerIn 𝓤 ⊓ centralizer (prodFactorTwo ψ : Set G) = ⊥ := by
    refine eq_bot_iff.2 fun z hz => ?_
    rw [← hS.F1_inf_centralizer_X2 hk hψt hZ]
    exact mem_inf.2 ⟨hZF1 (mem_inf.1 hz).1, (mem_inf.1 hz).2⟩
  have hScard : Nat.card W₂ = Nat.card k := by
    rw [hW2card, Nat.card_eq_fintype_card, hk]
  have hfixS : Nat.card (CFSG.centerIn 𝓤 ⊓ centralizer ((W₂ : Subgroup G) : Set G) :
      Subgroup G) = 2 ^ (2 * f) := by
    rw [hW₂, hS.centerIn_U_inf_centralizer_W2 hk, hS.card_E, ← pow_mul, mul_comm]
  have hJcard : Nat.card T₂ = Nat.card k - 1 := by rw [hT2card, Nat.card_eq_fintype_card, hk]
  have htransE : ∀ a ∈ miyamotoEG h L η Q, ∀ b ∈ miyamotoEG h L η Q, a ≠ 1 → b ≠ 1 →
      ∃ j ∈ T₂, j * a * j⁻¹ = b := by
    intro a ha b hb ha1 hb1
    have hEeq := hS.centerIn_U_inf_centralizer_W2 (ψ := ψ) hk
    exact Common.natural_module_exists_conj_of_le_normalizer hk' (Common.prodFactorTwoEquiv ψ)
      hcommZ hXA hcardZ hfixZ inf_le_right hScard hfixS hT2X hT2N hJcard hT2inf
      (by rw [hEeq]; exact ha) (by rw [hEeq]; exact hb) ha1 hb1
  have hT2E : T₂ ≤ normalizer (miyamotoEG h L η Q : Set G) := by
    intro x hx
    rw [← hS.centerIn_U_inf_centralizer_W2 (ψ := ψ) hk]
    exact mem_normalizer_inf (hXA (hT2X hx)) (mem_normalizer_centralizer (hT2N hx))
  set E := miyamotoEG h L η Q with hEdef
  have hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a :=
    fun a ha b hb => hS.F1_comm (hS.E_le_F1 ha) (hS.E_le_F1 hb)
  let : CommGroup E :=
    { (inferInstance : Group E) with mul_comm := fun a b => Subtype.ext (hEc a a.2 b b.2) }
  set ρ : normalizer (E : Set G) →* MulAut E := E.normalizerMonoidHom with hρ
  have hρapp : ∀ (g : normalizer (E : Set G)) (e : E),
      ((ρ g e : E) : G) = (g : G) * e * (g : G)⁻¹ := fun g e => rfl
  set J : Subgroup (MulAut E) := (T₂.subgroupOf (normalizer (E : Set G))).map ρ with hJ
  have hmemJ : ∀ x (hx : x ∈ T₂), ρ ⟨x, hT2E hx⟩ ∈ J := fun x hx => ⟨⟨x, hT2E hx⟩, hx, rfl⟩
  have hJab : ∀ a ∈ J, ∀ b ∈ J, a * b = b * a := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hT2c _ hx _ hy)
  have hJtrans : ∀ v w : E, v ≠ 1 → w ≠ 1 → ∃ a ∈ J, a v = w := by
    intro v w hv hw
    obtain ⟨j, hj, hjv⟩ := htransE v v.2 w w.2 (fun e => hv (Subtype.ext e))
      (fun e => hw (Subtype.ext e))
    exact ⟨ρ ⟨j, hT2E hj⟩, hmemJ j hj, Subtype.ext (by rw [hρapp]; exact hjv)⟩
  have hEcard : Nat.card E = (2 ^ f) ^ 2 := hS.card_E
  have htE : t ∈ normalizer (E : Set G) :=
    hS.normalizer_P1_le_normalizer_E hS.t_mem_normalizer_P1
  set σ := ρ ⟨t, htE⟩ with hσ
  have htt : t * t = 1 := hS.t_mul_t
  have hti : t⁻¹ = t := hS.t_inv
  have hσ2 : σ * σ = 1 := by
    rw [hσ, ← map_mul, ← map_one ρ]
    congr 1
    exact Subtype.ext htt
  have hσ1 : σ ≠ 1 := by
    intro hσ1
    have hEP : E ≤ miyamotoZG h L η := by
      rw [← hS.E_inf_PG]
      intro e he
      refine mem_inf.2 ⟨he, ?_⟩
      rw [← hS.RG_inf_C]
      refine mem_inf.2 ⟨hS.E_le_RG he, mem_centralizer_singleton_iff.2 ?_⟩
      have := congrArg Subtype.val (DFunLike.congr_fun hσ1 ⟨e, he⟩)
      rw [hσ, hρapp, MulAut.one_apply] at this
      calc e * t = (t * e * t⁻¹) * t := by rw [this]
        _ = t * e := by group
    have := Subgroup.card_le_of_le hEP
    rw [hEcard, card_miyamotoZG] at this
    have h4 := hS.four_le
    nlinarith
  have hσJ : ∀ a ∈ J, σ⁻¹ * a * σ ∈ J := by
    rintro _ ⟨⟨x, hxN⟩, hx, rfl⟩
    have hx' : x ∈ T₂ := hx
    have hxtN : t⁻¹ * x * t ∈ normalizer (E : Set G) :=
      mul_mem (mul_mem (inv_mem htE) (hT2E hx')) htE
    have e1 : σ⁻¹ * ρ ⟨x, hxN⟩ * σ = ρ ⟨t⁻¹ * x * t, hxtN⟩ := by
      rw [hσ, ← map_inv, ← map_mul, ← map_mul]
      rfl
    rw [e1]
    refine mem_of_commute_of_transitive hJab hJtrans fun b hb => ?_
    obtain ⟨⟨y, hyN⟩, hy, rfl⟩ := hb
    have hy' : y ∈ T₂ := hy
    have hxt : t⁻¹ * x * t ∈ prodFactorOne ψ := hS.t_conj_mem_X1 hψt (hT2X hx')
    have hc : (t⁻¹ * x * t) * y = y * (t⁻¹ * x * t) :=
      mem_centralizer_iff.1 (Common.prodFactorTwo_le_centralizer ψ (hT2X hy')) _ hxt
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hc
  have key := conj_eq_pow_of_transitive hEcard hJab hJtrans hσ2 hσ1 hσJ
  have huT : ∀ x ∈ T₂, u * x * u⁻¹ = x ^ 2 ^ f := by
    rintro _ ⟨⟨d, hd⟩, rfl⟩
    have hdD : (d : G) ∈ miyamotoDG h L η := hd
    show u * prodSnd ψ d * u⁻¹ = prodSnd ψ d ^ 2 ^ f
    rw [conj_prodSnd hX1 hX2 d (d ^ 2 ^ f) (by rw [SubgroupClass.coe_pow, hD _ hdD]), map_pow]
  have hui : u⁻¹ = u := inv_eq_of_mul_eq_one_right huu
  set τ := ρ ⟨u, huE⟩ with hτ
  have hτJ : ∀ x (hx : x ∈ T₂), τ⁻¹ * ρ ⟨x, hT2E hx⟩ * τ = ρ ⟨x, hT2E hx⟩ ^ 2 ^ f := by
    intro x hx
    rw [hτ, ← map_inv, ← map_mul, ← map_mul, ← map_pow]
    congr 1
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, SubgroupClass.coe_pow]
    rw [hui, ← huT x hx, hui]
  have hT2pow : ∀ x ∈ T₂, x ^ ((2 ^ f) ^ 2) = x := by
    intro x hx
    have h1 : x ^ ((2 ^ f) ^ 2 - 1) = 1 := by
      rw [← hT2card]
      have : (⟨x, hx⟩ : T₂) ^ Nat.card T₂ = 1 := pow_card_eq_one'
      exact congrArg Subtype.val this
    have h2 : (2 ^ f) ^ 2 = ((2 ^ f) ^ 2 - 1) + 1 := by
      have : 1 ≤ (2 ^ f) ^ 2 := Nat.one_le_pow _ _ (by positivity)
      omega
    rw [h2, pow_succ, h1, one_mul]
  set g := ρ ⟨t * u, mul_mem htE huE⟩ with hg
  have hgστ : g = σ * τ := by rw [hg, hσ, hτ, ← map_mul]; rfl
  have hgc : ∀ a ∈ J, g * a = a * g := by
    rintro _ ⟨⟨x, hxN⟩, hx, rfl⟩
    have hx' : x ∈ T₂ := hx
    have h1 : g⁻¹ * ρ ⟨x, hxN⟩ * g = ρ ⟨x, hxN⟩ := by
      rw [hgστ, mul_inv_rev, show τ⁻¹ * σ⁻¹ * ρ ⟨x, hxN⟩ * (σ * τ) =
        τ⁻¹ * (σ⁻¹ * ρ ⟨x, hxN⟩ * σ) * τ by group, key _ (hmemJ x hx')]
      have h2 : τ⁻¹ * ρ ⟨x, hxN⟩ ^ 2 ^ f * τ = (τ⁻¹ * ρ ⟨x, hxN⟩ * τ) ^ 2 ^ f := by
        have := map_pow (MulAut.conj τ⁻¹) (ρ ⟨x, hxN⟩) (2 ^ f)
        simpa only [MulAut.conj_apply, inv_inv] using this
      rw [h2, hτJ x hx', ← pow_mul, ← sq, ← map_pow]
      congr 1
      exact Subtype.ext (by simp only [SubgroupClass.coe_pow]; exact hT2pow x hx')
    calc g * ρ ⟨x, hxN⟩ = g * (g⁻¹ * ρ ⟨x, hxN⟩ * g) := by rw [h1]
      _ = ρ ⟨x, hxN⟩ * g := by group
  have hg2 : g ^ 2 ^ 1 = 1 := by
    rw [pow_one, sq, hg, ← map_mul, ← map_one ρ]
    congr 1
    apply Subtype.ext
    show t * u * (t * u) = 1
    rw [show t * u * (t * u) = t * (u * t) * u by group, hut,
      show t * (t * u) * u = (t * t) * (u * u) by group, htt, huu, one_mul]
  have hg1 := eq_one_of_commute_of_pow_two_pow_eq_one (m := 2 * f)
    (by rw [hEcard, ← pow_mul, mul_comm]) hJab hJtrans hgc hg2
  rw [mem_centralizer_iff]
  intro e he
  have := congrArg Subtype.val (DFunLike.congr_fun hg1 ⟨e, he⟩)
  rw [hg, hρapp, MulAut.one_apply] at this
  calc e * (t * u) = (t * u * e * (t * u)⁻¹) * (t * u) := by rw [this]
    _ = t * u * e := by group

theorem card_lt_card_F1_inf_centralizer [Fintype k] (hS : Setting h L η t Q T)
    (hk : Fintype.card k = (2 ^ f) ^ 2)
    (hψt : ∀ (x y : miyamotoM1G h L η t) (y₁ y₂ : SL(2, k)), (y : G) = t⁻¹ * x * t →
      ψ x = (y₁, y₂) → ψ y = (y₂, y₁))
    (hZF : CFSG.centerIn 𝓤 ≤ miyamotoFG h L η t Q) {v : G} (hvv : v * v = 1)
    (hvE : v ∈ centralizer (miyamotoEG h L η Q : Set G))
    (hvr : v * miyamotoR1G h L η = miyamotoR1G h L η * v)
    (hvZ : ∀ z ∈ CFSG.centerIn 𝓤, v * z * v⁻¹ ∈ (CFSG.centerIn 𝓤).map (MulAut.conj t).toMonoidHom) :
    (2 ^ f) ^ 4 < Nat.card (miyamotoF1G h L η t ⊓ centralizer ({v} : Set G) : Subgroup G) := by
  set Z := CFSG.centerIn 𝓤 with hZdef
  set Zt := Z.map (MulAut.conj t).toMonoidHom with hZt
  set E := miyamotoEG h L η Q with hEdef
  have hZE : Z ⊓ Zt = E := hS.centerIn_U_inf_t hk hψt
  have hFeq : miyamotoFG h L η t Q = Z ⊔ Zt := hS.F_eq_centerIn_U_sup_t hk hψt hZF
  have hZtF : Zt ≤ miyamotoFG h L η t Q := hFeq ▸ le_sup_right
  have hFF1 := hS.F_le_F1
  have hvi : v⁻¹ = v := inv_eq_of_mul_eq_one_right hvv
  have hvzF : ∀ z ∈ Z, v * z * v⁻¹ ∈ miyamotoF1G h L η t := fun z hz => hFF1 (hZtF (hvZ z hz))
  have hzF : ∀ z ∈ Z, z ∈ miyamotoF1G h L η t := fun z hz => hFF1 (hZF hz)
  let φ : Z →* G :=
    { toFun := fun z => (z : G) * (v * z * v⁻¹)
      map_one' := by simp
      map_mul' := fun a b => by
        simp only [Subgroup.coe_mul]
        have hc : (b : G) * (v * a * v⁻¹) = (v * a * v⁻¹) * b :=
          hS.F1_comm (hzF b b.2) (hvzF a a.2)
        calc (a : G) * b * (v * (a * b) * v⁻¹) = a * (b * (v * a * v⁻¹)) * (v * b * v⁻¹) := by
              group
          _ = a * ((v * a * v⁻¹) * b) * (v * b * v⁻¹) := by rw [hc]
          _ = a * (v * a * v⁻¹) * (b * (v * b * v⁻¹)) := by group }
  have hφ : ∀ z : Z, φ z = (z : G) * (v * z * v⁻¹) := fun z => rfl
  have hker : ∀ z : Z, φ z = 1 → (z : G) ∈ E := by
    intro z hz
    rw [hφ] at hz
    have h1 : v * z * v⁻¹ = (z : G)⁻¹ := eq_inv_of_mul_eq_one_right hz
    have hzi : (z : G)⁻¹ = z := inv_eq_of_mul_eq_one_right (hS.F1_mul_self _ (hzF z z.2))
    rw [← hZE]
    refine mem_inf.2 ⟨z.2, ?_⟩
    have := hvZ z z.2
    rwa [h1, hzi] at this
  have himE : ∀ z : Z, φ z ∈ E → φ z = 1 := by
    intro z hz
    rw [hφ] at hz ⊢
    have hEZ : E ≤ Z := hS.E_le_centerIn_U
    have hvz : v * z * v⁻¹ ∈ Z := by
      have := mul_mem (inv_mem (z.2)) (hEZ hz)
      rwa [inv_mul_cancel_left] at this
    have hvzE : v * z * v⁻¹ ∈ E := by
      rw [← hZE]
      exact mem_inf.2 ⟨hvz, hvZ z z.2⟩
    have hzE : (z : G) ∈ E := by
      have hc := mem_centralizer_iff.1 hvE _ hvzE
      have e2 : (z : G) = v * z * v⁻¹ := by
        calc (z : G) = v⁻¹ * ((v * z * v⁻¹) * v) := by group
          _ = v⁻¹ * (v * (v * z * v⁻¹)) := by rw [hc]
          _ = v * z * v⁻¹ := by group
      rw [e2]
      exact hvzE
    have hvc : v * z * v⁻¹ = z := by
      rw [← mem_centralizer_iff.1 hvE z hzE, mul_inv_cancel_right]
    rw [hvc]
    exact hS.F1_mul_self _ (hzF z z.2)
  set I := φ.range with hI
  have hIC : I ≤ miyamotoFG h L η t Q ⊓ centralizer ({v} : Set G) := by
    rintro _ ⟨z, rfl⟩
    refine mem_inf.2 ⟨mul_mem (hZF z.2) (hZtF (hvZ z z.2)), mem_centralizer_singleton_iff.2 ?_⟩
    rw [hφ]
    have hc : (z : G) * (v * z * v⁻¹) = (v * z * v⁻¹) * z := hS.F1_comm (hzF z z.2) (hvzF z z.2)
    have hva : v * (v * z * v⁻¹) * v⁻¹ = z := by
      rw [hvi]
      calc v * (v * ↑z * v) * v = (v * v) * z * (v * v) := by group
        _ = z := by rw [hvv]; group
    have e : v * ((z : G) * (v * z * v⁻¹)) * v⁻¹ = (z : G) * (v * z * v⁻¹) := by
      calc v * ((z : G) * (v * z * v⁻¹)) * v⁻¹ = (v * z * v⁻¹) * (v * (v * z * v⁻¹) * v⁻¹) := by
            group
        _ = (v * z * v⁻¹) * z := by rw [hva]
        _ = (z : G) * (v * z * v⁻¹) := hc.symm
    calc (z : G) * (v * z * v⁻¹) * v = (v * ((z : G) * (v * z * v⁻¹)) * v⁻¹) * v := by rw [e]
      _ = v * ((z : G) * (v * z * v⁻¹)) := by group
  have hkerle : φ.ker.map Z.subtype ≤ E := by
    rintro _ ⟨z, hz, rfl⟩
    exact hker z hz
  have hcardker : Nat.card φ.ker ≤ (2 ^ f) ^ 2 := by
    have := Subgroup.card_le_of_le hkerle
    rwa [card_map_of_injective Z.subtype_injective, hS.card_E] at this
  have hZcard : Nat.card Z = (2 ^ f) ^ 4 := (hS.F1_eq_centerIn_U_sup_r1 hk hψt hZF).1
  have hmul : Nat.card Z = Nat.card φ.ker * Nat.card I := by
    calc Nat.card Z = Nat.card φ.ker * φ.ker.index := (card_mul_index _).symm
      _ = Nat.card φ.ker * Nat.card I := by rw [index_ker]
  have hIcard : (2 ^ f) ^ 2 ≤ Nat.card I := by
    have hpos : 0 < (2 ^ f) ^ 2 := by positivity
    by_contra hlt
    push Not at hlt
    have : Nat.card Z < (2 ^ f) ^ 2 * (2 ^ f) ^ 2 := by
      rw [hmul]
      calc Nat.card φ.ker * Nat.card I ≤ (2 ^ f) ^ 2 * Nat.card I := Nat.mul_le_mul_right _ hcardker
        _ < (2 ^ f) ^ 2 * (2 ^ f) ^ 2 := Nat.mul_lt_mul_of_pos_left hlt hpos
    rw [hZcard] at this
    have e : (2 ^ f) ^ 2 * (2 ^ f) ^ 2 = (2 ^ f) ^ 4 := by ring
    omega
  have hIN : I ≤ normalizer (E : Set G) := fun x hx =>
    mem_normalizer_of_mem_centralizer' (mem_centralizer_iff.2 fun e he =>
      hS.F1_comm (hS.E_le_F1 he) (hFF1 (hIC hx).1))
  have hEI : E ⊓ I = ⊥ := by
    refine eq_bot_iff.2 ?_
    rintro _ ⟨he, ⟨z, rfl⟩⟩
    rw [himE z he]
    exact one_mem _
  have h1 := card_sup_mul_card_inf_eq hIN
  rw [hEI, card_bot, mul_one, hS.card_E] at h1
  set r := miyamotoR1G h L η with hr
  set Er := E.map (MulAut.conj r⁻¹).toMonoidHom with hEr
  have hErC : Er ≤ centralizer ({v} : Set G) := by
    rintro _ ⟨e, he, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    rw [mem_centralizer_singleton_iff]
    have hve : v * e = e * v := (mem_centralizer_iff.1 hvE e he).symm
    have hvr' : v * r⁻¹ = r⁻¹ * v := by
      calc v * r⁻¹ = r⁻¹ * (r * v) * r⁻¹ := by group
        _ = r⁻¹ * (v * r) * r⁻¹ := by rw [hvr]
        _ = r⁻¹ * v := by group
    calc r⁻¹ * e * r * v = r⁻¹ * e * (v * r) := by rw [mul_assoc, ← hvr]
      _ = r⁻¹ * (e * v) * r := by group
      _ = r⁻¹ * (v * e) * r := by rw [hve]
      _ = (r⁻¹ * v) * e * r := by group
      _ = (v * r⁻¹) * e * r := by rw [hvr']
      _ = v * (r⁻¹ * e * r) := by group
  have hErcard : Nat.card Er = (2 ^ f) ^ 2 := by
    rw [hEr, card_map_of_injective (MulAut.conj r⁻¹).injective, hS.card_E]
  set X := E ⊔ I with hX
  have hXF : X ≤ miyamotoFG h L η t Q := sup_le (hS.E_le_F) (fun x hx => (hIC hx).1)
  have hXC : X ≤ centralizer ({v} : Set G) := sup_le (fun e he =>
    mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 hvE e he)) (fun x hx => (hIC hx).2)
  have hErN : Er ≤ normalizer (X : Set G) := fun x hx =>
    mem_normalizer_of_mem_centralizer' (mem_centralizer_iff.2 fun y hy =>
      hS.F1_comm (hFF1 (hXF hy)) (hS.E_r1_le_F1 hx))
  have h2 := card_sup_mul_card_inf_eq hErN
  have hXEr : X ⊓ Er = ⊥ := by
    refine eq_bot_iff.2 fun x hx => ?_
    have := hS.E_r1_inf_F
    rw [← this]
    exact mem_inf.2 ⟨(mem_inf.1 hx).2, hXF (mem_inf.1 hx).1⟩
  rw [hXEr, card_bot, mul_one, hErcard] at h2
  have hle : X ⊔ Er ≤ miyamotoF1G h L η t ⊓ centralizer ({v} : Set G) :=
    sup_le (le_inf (hXF.trans hFF1) hXC) (le_inf (hS.E_r1_le_F1) hErC)
  have h3 := Subgroup.card_le_of_le hle
  have hXcard : (2 ^ f) ^ 4 ≤ Nat.card X := by
    rw [hX, h1]
    calc (2 ^ f) ^ 4 = (2 ^ f) ^ 2 * (2 ^ f) ^ 2 := by ring
      _ ≤ (2 ^ f) ^ 2 * Nat.card I := Nat.mul_le_mul_left _ hIcard
  have hq := hS.four_le
  have hq2 : 1 < (2 ^ f) ^ 2 := Nat.one_lt_pow two_ne_zero (by omega)
  calc (2 ^ f) ^ 4 < (2 ^ f) ^ 4 * (2 ^ f) ^ 2 := by
        exact lt_mul_of_one_lt_right (by positivity) hq2
    _ ≤ Nat.card X * (2 ^ f) ^ 2 := Nat.mul_le_mul_right _ hXcard
    _ = Nat.card (X ⊔ Er : Subgroup G) := h2.symm
    _ ≤ _ := h3

end Setting

end CFSG.LocalAnalysis.EvenBN.U4
