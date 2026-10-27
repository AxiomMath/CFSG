module

public import CFSG.Quasithin.H13.A5Producer
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5Inputs
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.StatementsFSU

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model CFSG.Blueprint
open scoped Pointwise

section Exist

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L : Subgroup G}

theorem exists_setting_F4 (h132two : Stmt13_3_2_two_F4) (h132fsu : Stmt13_3_2_three_fsu_F4)
    (h132A5 : Stmt13_3_2_three_A5_F4) (h : QTH13 G T L)
    (hA5 : quasithinO2QuotientIso L (alternatingGroup (Fin 5))) :
    ∃ V : Subgroup G, Nonempty (Setting G T L V) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hTN, hmax, hMmax, huniq⟩ := h132two G T L h L h.faithful
  have uniqueM : IsUniqueM (L ⊔ T) (Subgroup.normalizer (L : Set G)) :=
    ⟨⟨hMmax, sup_le Subgroup.le_normalizer hTN⟩, fun M' hM' => huniq M' hM'.1 hM'.2⟩
  obtain ⟨⟨V, hV⟩, hall⟩ := h132fsu G T L h L h.faithful
  obtain ⟨hVT, hTV, hfsu⟩ := hall V hV
  obtain ⟨R⟩ := h132A5 G T L h L h.faithful hA5 V hV
  have hVne : V ≠ ⊥ := hV.2.1

  have hab : IsElemAbelian 2 V := by
    refine ⟨⟨⟨fun a b => R.ψ.injective (by rw [map_mul, map_mul, mul_comm])⟩⟩, fun x hx => ?_⟩
    have hx2 : (⟨x, hx⟩ : ↥V) * ⟨x, hx⟩ = 1 := by
      apply R.ψ.injective
      rw [map_mul, map_one]
      show Multiplicative.ofAdd (Multiplicative.toAdd (R.ψ ⟨x, hx⟩) +
        Multiplicative.toAdd (R.ψ ⟨x, hx⟩)) = 1
      rw [Ev_add_self]
      rfl
    have := congrArg Subtype.val hx2
    simpa [pow_two] using this
  have hV2 : IsPGroup 2 V := fun g => ⟨1, Subtype.ext (by simpa using hab.2 g g.2)⟩
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := R.hnorm
  have hLTV : L ⊔ T ≤ Subgroup.normalizer (V : Set G) := sup_le hLV hTV

  have hNL : Subgroup.normalizer (V : Set G) ≤ Subgroup.normalizer (L : Set G) := by
    obtain ⟨M', hM', hM'le⟩ := exists_maxTwoLocal_ge
      (⟨V, hVne, hV2, rfl⟩ : IsTwoLocal (Subgroup.normalizer (V : Set G)))
    have := uniqueM.2 M' ⟨hM', hLTV.trans hM'le⟩
    exact this ▸ hM'le
  have hsylLT : IsSylowTwoOf T (L ⊔ T) := isSylowTwoOf_of_le h.sylow le_sup_right
  have hsylL : IsSylowTwoOf (T ⊓ L) L :=
    A4.isSylowTwoOf_inf_normal hsylLT le_sup_left (sup_le Subgroup.le_normalizer hTN)
  obtain ⟨F⟩ := exists_frame R hNL h.sylow.1 hTV hsylL

  have hO2 : pCoreOf 2 (L ⊔ T) ≤ Subgroup.centralizer (V : Set G) :=
    F.le_centralizer (CFSG.LieType.BorelTits.pCoreOf_le 2 _)
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _) fun d hd => by
        obtain ⟨k, hk⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (L ⊔ T) ⟨d, hd⟩
        exact ⟨k, by
          have := congrArg Subtype.val hk
          simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one] at this
          rw [this]
          exact Subgroup.one_mem _⟩

  have hCL : ∀ x ∈ L ⊓ Subgroup.centralizer (V : Set G), ∃ k : ℕ, x ^ 2 ^ k = 1 := by
    obtain ⟨φ, hφ, hker⟩ := hA5
    have hc1 : Nat.card ↥L = Nat.card φ.ker * 60 := by
      rw [← card_A5, ← Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective φ hφ).toEquiv,
        mul_comm]
      exact Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker
    have hc2 : Nat.card ↥L = Nat.card R.θ.ker * 60 := by
      rw [← card_A5, ← Nat.card_congr
        (QuotientGroup.quotientKerEquivOfSurjective R.θ R.surj).toEquiv, mul_comm]
      exact Subgroup.card_eq_card_quotient_mul_card_subgroup R.θ.ker
    have hle : φ.ker ≤ R.θ.ker := by
      intro x hx
      rw [hker] at hx
      rw [R.ker_eq, Subgroup.mem_subgroupOf]
      have hxO : (x : G) ∈ pCoreOf 2 L := ⟨x, hx, rfl⟩

      have hO2L : pCoreOf 2 L ≤ pCoreOf 2 (L ⊔ T) := by
        refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
          ((CFSG.LieType.BorelTits.pCoreOf_le 2 L).trans le_sup_left) ?_
          (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L)
        exact sup_le (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L)
          (hTN.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L))
      exact hO2 (hO2L hxO)
    have heq : φ.ker = R.θ.ker := Subgroup.eq_of_le_of_card_ge hle (by omega)
    intro x hx
    have hxk : (⟨x, hx.1⟩ : ↥L) ∈ φ.ker := by
      rw [heq, R.ker_eq, Subgroup.mem_subgroupOf]
      exact hx.2
    rw [hker] at hxk
    have hxO : x ∈ pCoreOf 2 L := ⟨⟨x, hx.1⟩, hxk, rfl⟩
    obtain ⟨k, hk⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L ⟨x, hxO⟩
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩

  have hC2 : IsPGroup 2 ↥((L ⊔ T) ⊓ Subgroup.centralizer (V : Set G)) := by
    rintro ⟨x, hxLT, hxC⟩
    have hx : x ∈ ((L : Set G) * (T : Set G)) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left L T hTN]
      exact hxLT
    obtain ⟨l, hl, t, ht, rfl⟩ := hx
    obtain ⟨a, ha⟩ := h.sylow.1 ⟨t, ht⟩
    have hta : t ^ 2 ^ a = 1 := by simpa using congrArg Subtype.val ha
    obtain ⟨l', hl', he⟩ := pow_mem_mul_of_normalizes hl (hTN ht) (2 ^ a)
    rw [hta, mul_one] at he
    have hC : (l * t) ^ 2 ^ a ∈ Subgroup.centralizer (V : Set G) :=
      Subgroup.pow_mem _ hxC _
    rw [he] at hC
    obtain ⟨k, hk⟩ := hCL l' ⟨hl', hC⟩
    refine ⟨a + k, Subtype.ext ?_⟩
    rw [SubmonoidClass.coe_pow, OneMemClass.coe_one, pow_add, pow_mul, he, hk]
  have hCn : L ⊔ T ≤
      Subgroup.normalizer (((L ⊔ T) ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    have key : ∀ g ∈ L ⊔ T, ∀ c, c ∈ (L ⊔ T) ⊓ Subgroup.centralizer (V : Set G) →
        g * c * g⁻¹ ∈ (L ⊔ T) ⊓ Subgroup.centralizer (V : Set G) := by
      intro g hg c hc
      refine ⟨(L ⊔ T).mul_mem ((L ⊔ T).mul_mem hg hc.1) ((L ⊔ T).inv_mem hg), ?_⟩
      show g * c * g⁻¹ ∈ Subgroup.centralizer (V : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      have hv' : g⁻¹ * v * g ∈ V :=
        (Subgroup.mem_normalizer_iff''.mp (hLTV hg) v).mp hv
      have hcomm := Subgroup.mem_centralizer_iff.mp hc.2 _ hv'
      calc v * (g * c * g⁻¹) = g * ((g⁻¹ * v * g) * c) * g⁻¹ := by group
        _ = g * (c * (g⁻¹ * v * g)) * g⁻¹ := by rw [hcomm]
        _ = g * c * g⁻¹ * v := by group
    intro c
    refine ⟨key g hg c, fun hc => ?_⟩
    simpa [mul_assoc] using key g⁻¹ ((L ⊔ T).inv_mem hg) _ hc
  have hcLT : (L ⊔ T) ⊓ Subgroup.centralizer (V : Set G) = pCoreOf 2 (L ⊔ T) :=
    le_antisymm
      (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left hCn hC2)
      (le_inf (CFSG.LieType.BorelTits.pCoreOf_le 2 _) hO2)
  exact ⟨V, ⟨{
    h13 := h
    a5 := hA5
    T_le_NL := hTN
    maximal := hmax
    uniqueM := uniqueM
    oTwoRes_L := oTwoRes_eq_of_faithful h.faithful
    charTwo_L := charTwo_of_faithful h.qtke.2.1 h.sylow h.faithful
    reduced := ⟨hVT.trans le_sup_right, hLTV, hab, fun D hDLT hDn hD2 =>
      F.le_centralizer hDLT hDn hD2⟩
    cLT := hcLT
    frame := F
    irr := hV
    fsu := hfsu }⟩⟩

end Exist

end CFSG.Quasithin.H13.A5
