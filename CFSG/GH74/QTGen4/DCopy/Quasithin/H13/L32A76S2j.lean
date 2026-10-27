module

public import CFSG.GH74.QTGen4.Finite4
public import CFSG.Quasithin.H13.L32A76S2j
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32A76S2b
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32A76S2d
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32A76S2g
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32A76S2h
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32A76S2i

public section

namespace CFSG.Quasithin.H13.L32A.S2

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits
open CFSG.Quasithin.H13.Q511 CFSG.Quasithin.H13.L32A.M76 CFSG.Quasithin.F7
open scoped commutatorElement

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

variable {T L V H Y : Subgroup G} {γ γ' : F8.Geom T L H} {g : ↥((L ⊔ T) ⊔ H)}

namespace Ctx_F4
open CFSG.Quasithin.H13.L32A.S2.Ctx_F4

variable (C : Ctx_F4 G T L V H Y)
include C

theorem comm_LA_K_F4 [Fact (IsElemAbelian 2 (tildeOf (fsuV1 T V) (conjClosure V H)))]
    {e₁ e₂ b : MulAut ↥(tildeOf (fsuV1 T V) (conjClosure V H))}
    (D : Good_F4 C γ γ' g e₁ e₂ b) {LA : Subgroup G}
    (hNLA : Subgroup.normalizer ((⁅conjClosure V H, F8.Uγ V H (g : G)⁆ : Subgroup G) : Set G) ≤
      Subgroup.normalizer (LA : Set G))
    (hAut : ∀ x ∈ Subgroup.normalizer (LA : Set G),
      x ∈ Subgroup.centralizer ((⁅conjClosure V H, F8.Uγ V H (g : G)⁆ : Subgroup G) : Set G) →
      x ^ 5 = 1 → ∀ l ∈ LA, l * x * l⁻¹ * x⁻¹ ∈ pCoreOf 2 LA) :
    ∀ l ∈ LA, ∀ k ∈ oTwoUpper (C.Pe_F4 e₂), l * k * l⁻¹ * k⁻¹ ∈ pCoreOf 2 LA := by
  have hKC := C.K_le_centralizer_F4 D
  have hKN : oTwoUpper (C.Pe_F4 e₂) ≤ Subgroup.normalizer (LA : Set G) := fun k hk =>
    hNLA (Subgroup.mem_normalizer_fintype fun a ha => by
      rw [(Subgroup.mem_centralizer_iff.mp (hKC hk) a ha).symm, mul_inv_cancel_right]
      exact ha)
  have hON : ∀ x ∈ oTwoUpper (C.Pe_F4 e₂), ∀ y ∈ pCoreOf 2 LA, x * y * x⁻¹ ∈ pCoreOf 2 LA :=
    fun x hx y hy => (Subgroup.mem_normalizer_iff.mp
      (normalizer_le_normalizer_pCoreOf 2 LA (hKN hx)) y).mp hy
  intro l hl k hk
  induction hk using Subgroup.closure_induction with
  | mem x hx =>
    have hxK : x ∈ oTwoUpper (C.Pe_F4 e₂) := mem_oTwoUpper_of_odd hx.1 hx.2
    exact hAut x (hKN hxK) (hKC hxK) (C.pow_five_of_odd_F4 D.lines.h5₂ hx.1 hx.2) l hl
  | one =>
    have e : l * 1 * l⁻¹ * (1 : G)⁻¹ = 1 := by group
    rw [e]
    exact Subgroup.one_mem _
  | mul x y hx hy ihx ihy =>
    have e : l * (x * y) * l⁻¹ * (x * y)⁻¹ =
        (l * x * l⁻¹ * x⁻¹) * (x * (l * y * l⁻¹ * y⁻¹) * x⁻¹) := by group
    rw [e]
    exact Subgroup.mul_mem _ ihx (hON x hx _ ihy)
  | inv x hx ihx =>
    have e : l * x⁻¹ * l⁻¹ * x⁻¹⁻¹ = x⁻¹ * (l * x * l⁻¹ * x⁻¹)⁻¹ * x⁻¹⁻¹ := by group
    rw [e]
    exact hON x⁻¹ (Subgroup.inv_mem _ hx) _ (Subgroup.inv_mem _ ihx)

end Ctx_F4

namespace Ctx_F4
open CFSG.Quasithin.H13.L32A.S2.Ctx_F4

variable (C : Ctx_F4 G T L V H Y)
include C

theorem exists_TA_F4 [Fact (IsElemAbelian 2 (tildeOf (fsuV1 T V) (conjClosure V H)))]
    {e₁ e₂ b : MulAut ↥(tildeOf (fsuV1 T V) (conjClosure V H))}
    (D : Good_F4 C γ γ' g e₁ e₂ b) {S : Subgroup G} (hSH : S ≤ H) (hSsyl : quasithinIsSylowTwo S)
    (hUS : F8.Uγ V H (g : G) ≤ S) {LA : Subgroup G}
    (hLA : LA ∈ cComp (Subgroup.normalizer
      ((⁅conjClosure V H, F8.Uγ V H (g : G)⁆ : Subgroup G) : Set G)))
    (hNLA : Subgroup.normalizer ((⁅conjClosure V H, F8.Uγ V H (g : G)⁆ : Subgroup G) : Set G) ≤
      Subgroup.normalizer (LA : Set G))
    (htop : autOn LA ⁅conjClosure V H, F8.Uγ V H (g : G)⁆ = ⊤)
    (hAut : ∀ x ∈ Subgroup.normalizer (LA : Set G),
      x ∈ Subgroup.centralizer ((⁅conjClosure V H, F8.Uγ V H (g : G)⁆ : Subgroup G) : Set G) →
      x ^ 5 = 1 → ∀ l ∈ LA, l * x * l⁻¹ * x⁻¹ ∈ pCoreOf 2 LA) :
    ∃ TA : Subgroup G, quasithinIsSylowTwo TA ∧
      TA ≤ Subgroup.normalizer ((⁅conjClosure V H, F8.Uγ V H (g : G)⁆ : Subgroup G) : Set G) ∧
      TA ≤ Subgroup.normalizer (oTwoUpper (C.Pe_F4 e₂) : Set G) ∧
      LA ≤ Subgroup.normalizer (oTwoUpper (C.Pe_F4 e₂) : Set G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set A : Subgroup G := ⁅conjClosure V H, F8.Uγ V H (g : G)⁆ with hAdef
  set K := oTwoUpper (C.Pe_F4 e₂) with hKdef
  set S₁ := S ⊓ C.Ne_F4 e₁ with hS₁def
  have hL := D.lines
  have hAU : A ≤ conjClosure V H :=
    (C.h98.F913_3 D.s (X := V) (Y := V) (Or.inl rfl) (Or.inl rfl)).trans inf_le_left
  have hAel : IsElemAbelian 2 A := by
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => C.h98.F911_3.2 x (hAU hx)⟩
    have := C.h98.F911_3.1.is_comm.comm ⟨a, hAU a.2⟩ ⟨b, hAU b.2⟩
    have h2 : (a : G) * b = b * a := congrArg Subtype.val this
    simpa using h2
  have h8 : Nat.card A = 8 := D.card
  set NA := Subgroup.normalizer (A : Set G) with hNAdef
  have hLAN : LA ≤ NA := le_of_mem_cComp hLA

  have hS₁N : S₁ ≤ NA := C.S₁_le_normalizer_F4 D hSsyl.1 hUS
  have hS₁K : S₁ ≤ Subgroup.normalizer (K : Set G) := by
    intro t ht
    obtain ⟨htH, hte⟩ := (C.mem_Ne_F4).mp (C.Ne_le_Ne_F4 hL D.inE D.e₂E ht.2)
    exact normalizer_le_normalizer_oTwoUpper _ (C.mem_normalizer_Pe_F4 ⟨t, htH⟩ hte)
  have hS₁2 : IsPGroup 2 S₁ := hSsyl.1.to_le inf_le_left

  obtain ⟨TA, hS₁TA, hTA⟩ := exists_isSylowTwoOf_of_le hS₁N hS₁2
  have hTA2 : IsPGroup 2 TA := hTA.2.1
  set R := TA ⊓ LA with hRdef
  have hR : IsSylowTwoOf R LA := A4.isSylowTwoOf_inf_normal hTA hLAN hNLA
  have hRN : R ≤ NA := inf_le_left.trans hTA.1
  have hR8 : Nat.card (autOn R A) = 8 := card_autOn_sylow hAel h8 hLAN hR htop

  obtain ⟨⟨v₀, hv₀⟩, hv₀1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp
    (show fsuV1 T V ≠ ⊥ from fun h => by
      have := C.h98.card_V₁
      rw [h, Subgroup.card_bot] at this
      norm_num at this)
  have hv₀1' : v₀ ≠ 1 := fun h => hv₀1 (Subtype.ext h)
  have hV₁el : ∀ c ∈ fsuV1 T V, c = 1 ∨ c = v₀ := by
    intro c hc
    obtain ⟨p, q, hpq, hpq'⟩ := Nat.card_eq_two_iff.mp C.h98.card_V₁
    have hall : ∀ z : ↥(fsuV1 T V), z = p ∨ z = q := fun z => by
      have : z ∈ ({p, q} : Set _) := hpq' ▸ Set.mem_univ z
      simpa using this
    have h1o := hall 1
    have hv := hall ⟨v₀, hv₀⟩
    have hcz := hall ⟨c, hc⟩
    by_cases hc1 : c = 1
    · exact Or.inl hc1
    right
    have hc1' : (⟨c, hc⟩ : ↥(fsuV1 T V)) ≠ 1 := fun h => hc1 (congrArg Subtype.val h)
    have hz : (⟨c, hc⟩ : ↥(fsuV1 T V)) = ⟨v₀, hv₀⟩ := by
      rcases hcz with e1 | e1 <;> rcases hv with e2 | e2 <;> rcases h1o with e0 | e0 <;>
        first
          | exact e1.trans e2.symm
          | exact absurd (e1.trans e0.symm) hc1'
          | exact absurd (e2.trans e0.symm) hv₀1
    exact congrArg Subtype.val hz

  have hcommK := C.comm_LA_K_F4 D hNLA hAut
  have hRS₁ : Nat.card (autOn (R ⊓ S₁) A) ≤ 4 := by
    refine E8.card_le_four hAel h8 (v := ⟨v₀, D.V₁_le hv₀⟩)
      (fun h => hv₀1' (congrArg Subtype.val h)) ?_
    intro α hα a
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hα
    have hyR : (y : G) ∈ R ⊓ S₁ := hy
    have hyH : (y : G) ∈ H := (C.mem_Ne_F4).mp hyR.2.2 |>.1
    have hK : ∀ k : ↥H, (k : G) ∈ K →
        FixR.rho C.h91_F4 k * FixR.rho C.h91_F4 ⟨y, hyH⟩ =
          FixR.rho C.h91_F4 ⟨y, hyH⟩ * FixR.rho C.h91_F4 k := by
      intro k hk
      refine FixR.rho_comm_of_mem C.h91_F4 ?_
      have h1 : (k : G) * y * (k : G)⁻¹ * (y : G)⁻¹ ∈ K := by
        have hyK : (y : G) ∈ Subgroup.normalizer (K : Set G) := hS₁K hyR.2
        have := (Subgroup.mem_normalizer_iff.mp hyK _).mp (K.inv_mem hk)
        have e : (k : G) * y * (k : G)⁻¹ * (y : G)⁻¹ =
            (k : G) * ((y : G) * (k : G)⁻¹ * (y : G)⁻¹) := by group
        rw [e]
        exact K.mul_mem hk this
      have h2 : (k : G) * y * (k : G)⁻¹ * (y : G)⁻¹ ∈ pCoreOf 2 LA := by
        have := Subgroup.inv_mem _ (hcommK y hyR.1.2 k hk)
        have e : ((y : G) * k * (y : G)⁻¹ * (k : G)⁻¹)⁻¹ = (k : G) * y * (k : G)⁻¹ * (y : G)⁻¹ :=
          by group
        rwa [e] at this
      exact C.le_Q_of_isPGroup_F4 hL.h5₂ (X := K ⊓ pCoreOf 2 LA)
        (inf_le_left.trans (oTwoUpper_le _)) ((pCoreOf_isPGroup 2 LA).to_le inf_le_right) ⟨h1, h2⟩
    have hc := C.comm_mem_V₁_of_comm_F4 D hSsyl.1 hUS ⟨y, hyH⟩ hyR.2 hK a a.2
    rcases hV₁el _ hc with h | h
    · left
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_inv, conjAct_apply_coe']
      exact h
    · right
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_inv, conjAct_apply_coe']
      exact h

  have hRnS₁ : ¬ R ≤ S₁ := by
    intro h
    have : R ⊓ S₁ = R := inf_eq_left.mpr h
    rw [this, hR8] at hRS₁
    omega
  have hTAne : S₁ ≠ TA := fun h => hRnS₁ (h ▸ inf_le_left)

  have hidx : 2 ≤ S₁.relIndex TA := by
    have h1 : S₁.relIndex TA ≠ 1 := fun h =>
      hTAne (le_antisymm hS₁TA (Subgroup.relIndex_eq_one.mp h))
    obtain ⟨n, hn⟩ := hTA2.index (S₁.subgroupOf TA)
    have hn' : S₁.relIndex TA = 2 ^ n := hn
    rcases n with _ | n
    · exact absurd (by rw [hn', pow_zero]) h1
    · rw [hn', pow_succ]
      have : 1 ≤ 2 ^ n := Nat.one_le_two_pow
      omega
  have hcardTA : 2 * Nat.card S₁ ≤ Nat.card TA := by
    have := Subgroup.relIndex_mul_card S₁ TA
    rw [inf_eq_left.mpr hS₁TA] at this
    nlinarith [Nat.card_pos (α := S₁)]
  have hcardS : Nat.card S ≤ 2 * Nat.card S₁ := C.card_le_two_mul_F4 hL D.inE D.e₁E hSH
  have hTAle := card_le_of_isPGroup_of_quasithinIsSylowTwo hSsyl hTA2
  have hTAeq : Nat.card TA = Nat.card S := by omega
  have hTAsyl : quasithinIsSylowTwo TA := quasithinIsSylowTwo_of_card_eq hSsyl hTA2 hTAeq

  have hRS₁le : Nat.card R ≤ 2 * Nat.card ↥(R ⊓ S₁) := by
    have h1 : S₁.relIndex R ≤ S₁.relIndex TA :=
      Subgroup.relIndex_le_of_le_right inf_le_left Subgroup.index_ne_zero_of_finite
    have h2 : S₁.relIndex TA = 2 := by
      have := Subgroup.relIndex_mul_card S₁ TA
      rw [inf_eq_left.mpr hS₁TA] at this
      have h3 : Nat.card TA = 2 * Nat.card S₁ := by omega
      rw [h3, mul_comm] at this
      exact Nat.eq_of_mul_eq_mul_left Nat.card_pos (this.trans (mul_comm _ _))
    have h3 := Subgroup.relIndex_mul_card S₁ R
    rw [inf_comm] at h3
    rw [← h3]
    exact Nat.mul_le_mul_right _ (h1.trans h2.le)
  have hCR : R ⊓ Subgroup.centralizer (A : Set G) ≤ S₁ := by
    have e1 := card_eq_card_autOn_mul hRN
    have e2 := card_eq_card_autOn_mul (X := R ⊓ S₁) (A := A) (inf_le_left.trans hRN)
    rw [hR8] at e1
    have hle : (R ⊓ S₁) ⊓ Subgroup.centralizer (A : Set G) ≤ R ⊓ Subgroup.centralizer (A : Set G) :=
      inf_le_inf_right _ inf_le_left
    have hcard : Nat.card ↥(R ⊓ Subgroup.centralizer (A : Set G)) ≤
        Nat.card ↥((R ⊓ S₁) ⊓ Subgroup.centralizer (A : Set G)) := by
      have h4 : Nat.card ↥(R ⊓ S₁) ≤ 4 * Nat.card ↥((R ⊓ S₁) ⊓ Subgroup.centralizer (A : Set G)) :=
        by rw [e2]; exact Nat.mul_le_mul_right _ hRS₁
      have hpos : 0 < Nat.card ↥(R ⊓ Subgroup.centralizer (A : Set G)) := Nat.card_pos
      nlinarith
    have heq := Subgroup.eq_of_le_of_card_ge hle hcard
    rw [← heq]
    exact inf_le_left.trans inf_le_right
  have hOLA : pCoreOf 2 LA ≤ S₁ := by
    refine le_trans (le_inf ?_ ?_) hCR
    · refine le_inf ?_ (pCoreOf_le 2 LA)
      have hON : NA ≤ Subgroup.normalizer (pCoreOf 2 LA : Set G) :=
        hNLA.trans (normalizer_le_normalizer_pCoreOf 2 LA)
      exact (le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 LA).trans hLAN) hON
        (pCoreOf_isPGroup 2 LA)).trans (pCoreOf_two_le_of_isSylowTwoOf hTA)
    · refine le_centralizer_of_autOn_eq_bot ((pCoreOf_le 2 LA).trans hLAN) ?_
      refine E8.eq_bot_of_isPGroup_of_normal hAel h8 ?_ ?_
      · refine ⟨fun α hα β => ?_⟩
        have hβ : β ∈ autOn LA A := htop ▸ Subgroup.mem_top β
        obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hβ
        obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hα
        refine Subgroup.mem_map.mpr ⟨y * z * y⁻¹, ?_, by simp⟩
        have hzO : (z : G) ∈ pCoreOf 2 LA := hz
        have hyL : (y : G) ∈ LA := hy
        show (y : G) * z * (y : G)⁻¹ ∈ pCoreOf 2 LA
        exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 LA hyL) _).mp hzO
      · exact ((pCoreOf_isPGroup 2 LA).comap_of_injective NA.subtype
          NA.subtype_injective).map (conjAct A)

  have hLAK : LA ≤ Subgroup.normalizer (K : Set G) := by
    intro l hl
    refine Subgroup.mem_normalizer_fintype ?_
    exact conj_mem_oTwoUpper_of_comm (pCoreOf_isPGroup 2 LA) (hOLA.trans hS₁K)
      (fun x hx => hcommK l hl x hx)

  have hTAK : TA ≤ Subgroup.normalizer (K : Set G) := by
    have hsup : S₁ ⊔ R = TA := by
      refine le_antisymm (sup_le hS₁TA inf_le_left) ?_
      have hlt : S₁ < S₁ ⊔ R := lt_of_le_of_ne le_sup_left fun h => hRnS₁ (h ▸ le_sup_right)
      have h1 : 2 ≤ S₁.relIndex (S₁ ⊔ R) := by
        have hne : S₁.relIndex (S₁ ⊔ R) ≠ 1 := fun h =>
          hlt.ne (le_antisymm le_sup_left (Subgroup.relIndex_eq_one.mp h))
        have hpos : S₁.relIndex (S₁ ⊔ R) ≠ 0 := Subgroup.index_ne_zero_of_finite
        omega
      have h2 := Subgroup.relIndex_mul_card S₁ (S₁ ⊔ R)
      rw [inf_eq_left.mpr le_sup_left] at h2
      have h3 : Nat.card TA ≤ Nat.card ↥(S₁ ⊔ R) := by
        have := Nat.card_pos (α := ↥S₁)
        nlinarith
      exact (Subgroup.eq_of_le_of_card_ge (sup_le hS₁TA inf_le_left) h3).ge
    rw [← hsup]
    exact sup_le hS₁K (inf_le_right.trans hLAK)
  exact ⟨TA, hTAsyl, hTA.1, hTAK, hLAK⟩

end Ctx_F4

end CFSG.Quasithin.H13.L32A.S2

end
