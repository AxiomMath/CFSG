module

public import CFSG.Quasithin.H13.U3L15L
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A6Inputs13_3
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.U3L15Gen

public section

namespace CFSG.Quasithin.H13.U3

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open scoped IsMulCommutative commutatorElement

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

theorem u3Stmt13_3_15_of_L32_F4 (h1332 : Stmt13_3_2_F4) (h13314 : A6.Stmt13_3_14_F4)
    {T L V V₂ X I₂ : Subgroup G} [IsMulCommutative ↥V] (hH : QTH13 G T L)
    (hL3 : LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 3 2 1)
    (hnat : BinaryNaturalSL (V := ↥V) (autOn L V) ⊤ ⊥ 3 1)
    (hV : IsIrrPlusIn L (reducedAggregate (L ⊔ T)) T V)
    (hzv : V ⊓ centralizer (L : Set G) = ⊥) (hV2 : A6.IsV2 T V V₂)
    (hX : X = L₁Of L V₂)
    (hI₂ : I₂ = conjClosure (pCoreOf 2 (A6.g1 T V)) (normalizer (V₂ : Set G))) :
    normalizer (V₂ : Set G) ≤ normalizer (I₂ : Set G) ∧
      I₂ = X ⊔ pCoreOf 2 (A6.g1 T V) ∧
      I₂ ⊓ centralizer (V₂ : Set G) = pCoreOf 2 I₂ ∧
      Nonempty (↥I₂ ⧸ CFSG.pCore 2 ↥I₂ ≃* Equiv.Perm (Fin 3)) ∧ oTwoRes I₂ = X ∧
      pCoreOf 2 (A6.g1 T V) ⊓ centralizer (V₂ : Set G) ≤ pCoreOf 2 I₂ ∧
      pCoreOf 2 I₂ ≤ pCoreOf 2 (normalizer (V₂ : Set G)) ∧
      CFSG.pRank 3 ↥(centralizer (V₂ : Set G)) ≤ 1 ∧
      ∀ V₃ : Subgroup G, V₂ ≤ V₃ → V₃ ≤ V → T ≤ normalizer (V₃ : Set G) →
        Nat.card V₃ = 8 →
          centralizer (V₃ : Set G) ≤ normalizer (V : Set G) ∧
            (¬ LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSU 3 3 1 →
              ⁅V, centralizer (V₃ : Set G)⁆ ≤ fsuV1 T V) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  subst hX
  obtain ⟨-, ⟨hTL, -⟩, ⟨-, hVall⟩, -⟩ := h1332 G T L hH L hH.faithful
  obtain ⟨-, hTV, -, -, -⟩ := hVall V hV
  obtain ⟨hVR, hV1, hLV, -, hVlt, -, -⟩ := id hV

  obtain ⟨e⟩ := nonempty_equiv_SL32_of_lieModel hL3
  have hsSL : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :=
    HSType.isSimpleGroup_SL_three_two
  have hs : IsSimpleGroup (↥L ⧸ CFSG.pCore 2 ↥L) := (MulEquiv.isSimpleGroup_congr e).2 hsSL
  have hna : ∃ a b : ↥L ⧸ CFSG.pCore 2 ↥L, a * b ≠ b * a := by
    have hna0 : ∃ a b : Matrix.SpecialLinearGroup (Fin 3) (ZMod 2), a * b ≠ b * a := by
      decide
    obtain ⟨a, b, hab⟩ := hna0
    refine ⟨e.symm a, e.symm b, fun h => hab ?_⟩
    simpa using congrArg e h
  have hcen := center_eq_bot_of_isSimpleGroup hna

  have hVf := fun v (hv : v ∈ V) => mem_reducedAggregate' (hVR hv)
  have hVC : V ≤ centralizer (pCoreOf 2 (L ⊔ T) : Set G) :=
    fun v hv => mem_centralizer_iff.2 fun k hk => (hVf v hv).2.1 k hk
  have hsq : ∀ v ∈ V, v * v = 1 := fun v hv => by rw [← pow_two]; exact (hVf v hv).2.2
  have hLC : ¬ L ≤ centralizer (V : Set G) := fun h =>
    (lt_irrefl _) (lt_of_lt_of_le hVlt (le_inf le_rfl (le_centralizer_iff.1 h)))
  have hOL : pCoreOf 2 L ≤ centralizer (V : Set G) :=
    (pCoreOf_le_pCoreOf_sup hTL).trans (le_centralizer_iff.1 hVC)
  have hK1 := inf_centralizer_subgroupOf_eq_pCore hs hLV hOL hLC
  have hCLO : L ⊓ centralizer (V : Set G) ≤ pCoreOf 2 L := by
    intro x hx
    have hx' : (⟨x, hx.1⟩ : ↥L) ∈ (L ⊓ centralizer (V : Set G)).subgroupOf L :=
      mem_subgroupOf.2 hx
    rw [hK1] at hx'
    exact coe_mem_pCoreOf_iff.2 hx'
  have hCL : IsPGroup 2 ↥(L ⊓ centralizer (V : Set G)) :=
    (LieType.BorelTits.pCoreOf_isPGroup 2 L).to_le hCLO
  have hZC : A6.o2Z L ≤ centralizer (V : Set G) :=
    (o2Z_le_pCoreOf_of_center_eq_bot hcen).trans hOL

  obtain ⟨D⟩ := BinaryNaturalSL.toL3Coord hnat
  have hV8 : Nat.card V = 8 := by
    have h := D.card_U
    rw [card_top, card_bot] at h
    exact h
  obtain ⟨h12, h2V, hT2, hc2⟩ := id hV2
  set β' : ↥V → Multiplicative L3.Vec := fun v => D.β ⟨v, mem_top v⟩ with hβ'
  have hβinj : Function.Injective β' := by
    intro x y hxy
    have h1 : D.β (⟨x, mem_top x⟩ * (⟨y, mem_top y⟩)⁻¹) = 1 := by
      rw [map_mul, map_inv]
      exact mul_inv_eq_one.2 hxy
    have h2 := (D.ker_β _).1 h1
    rw [mem_bot] at h2
    have h3 : x * y⁻¹ = 1 := h2
    exact mul_inv_eq_one.1 h3
  have hβrho : ∀ (γ : L3.Γ) (v : ↥V), β' (D.rho γ v) =
      Multiplicative.ofAdd (L3.act γ (Multiplicative.toAdd (β' v))) := by
    intro γ v
    exact D.β_rho γ v (mem_top v) (mem_top _)

  classical
  set W : Finset L3.Vec := Finset.univ.filter fun x => ∃ v : G, ∃ hv : v ∈ V₂,
    Multiplicative.toAdd (β' ⟨v, h2V hv⟩) = x with hW
  have hmemW : ∀ x, x ∈ W ↔ ∃ v : G, ∃ hv : v ∈ V₂, Multiplicative.toAdd (β' ⟨v, h2V hv⟩) = x :=
    fun x => by rw [hW, Finset.mem_filter]; simp
  have hβmul : ∀ x y : ↥V, β' (x * y) = β' x * β' y := fun x y => by
    simp only [hβ']
    rw [← map_mul]
    rfl
  have hWplane : isPlane W = true := by
    simp only [isPlane, Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · have h1 : Nat.card ↥V₂ = Nat.card ↥W := Nat.card_congr (Equiv.ofBijective
        (fun v : ↥V₂ => (⟨Multiplicative.toAdd (β' ⟨v, h2V v.2⟩),
          (hmemW _).2 ⟨v, v.2, rfl⟩⟩ : ↥W)) ⟨?_, ?_⟩)
      · rw [← Nat.card_eq_finsetCard, ← h1, hc2]
      · intro x y hxy
        have h1 := congrArg Subtype.val hxy
        simp only at h1
        have h2 := hβinj (Multiplicative.toAdd.injective h1)
        exact Subtype.ext (by simpa using congrArg (fun w : ↥V => (w : G)) h2)
      · rintro ⟨x, hx⟩
        obtain ⟨v, hv, rfl⟩ := (hmemW x).1 hx
        exact ⟨⟨v, hv⟩, rfl⟩
    · refine (hmemW 0).2 ⟨1, one_mem _, ?_⟩
      have : β' ⟨1, h2V (one_mem V₂)⟩ = 1 := map_one D.β
      rw [this]
      rfl
    · intro x hx y hy
      obtain ⟨v, hv, rfl⟩ := (hmemW x).1 hx
      obtain ⟨w, hw, rfl⟩ := (hmemW y).1 hy
      refine (hmemW _).2 ⟨v * w, mul_mem hv hw, ?_⟩
      have : (⟨v * w, h2V (mul_mem hv hw)⟩ : ↥V) = ⟨v, h2V hv⟩ * ⟨w, h2V hw⟩ := rfl
      rw [this, hβmul, toAdd_mul]
  obtain ⟨γ, hγ⟩ := cert_plane W hWplane
  simp only [goodGamma, Bool.and_eq_true, decide_eq_true_eq] at hγ
  obtain ⟨⟨hγ3, hγW⟩, hγm⟩ := hγ

  obtain ⟨⟨l, hlN⟩, hlL, hle⟩ := mem_map.1 (D.rho_mem γ)
  have hlL' : l ∈ L := mem_subgroupOf.1 hlL
  have hconj : ∀ v (hv : v ∈ V), l * v * l⁻¹ = (D.rho γ ⟨v, hv⟩ : G) := by
    intro v hv
    rw [← hle, A1b.conjAct_coe]
  have hlV2 : l ∈ normalizer (V₂ : Set G) := by
    refine mem_normalizer_of_forall_conj_mem fun v hv => ?_
    have hx := hγW _ ((hmemW _).2 ⟨v, hv, rfl⟩)
    obtain ⟨v', hv', he⟩ := (hmemW _).1 hx
    have h1 : β' ⟨v', h2V hv'⟩ = β' (D.rho γ ⟨v, h2V hv⟩) := by
      rw [hβrho]
      exact Multiplicative.toAdd.injective he
    have h2 := congrArg Subtype.val (hβinj h1)
    rw [hconj v (h2V hv), ← h2]
    exact hv'
  have hl3 : l ^ 3 ∈ centralizer (V : Set G) := by
    have h1 : conjAct V ⟨l ^ 3, pow_mem hlN 3⟩ = 1 := by
      have : (⟨l ^ 3, pow_mem hlN 3⟩ : normalizer (V : Set G)) = ⟨l, hlN⟩ ^ 3 := rfl
      rw [this, map_pow, hle, ← map_pow, hγ3, map_one]
    exact A1b.conjAct_eq_one_iff.1 h1
  have hlc : l ∉ centralizer (V₂ : Set G) := by
    intro h
    obtain ⟨w, hw, hwm⟩ := hγm
    obtain ⟨v, hv, rfl⟩ := (hmemW w).1 hw
    apply hwm
    have h1 : l * v * l⁻¹ = v := by
      rw [← (mem_centralizer_iff.1 h) v hv, mul_inv_cancel_right]
    have h2 : D.rho γ ⟨v, h2V hv⟩ = ⟨v, h2V hv⟩ := Subtype.ext (by rw [← hconj, h1])
    have h3 := hβrho γ ⟨v, h2V hv⟩
    rw [h2] at h3
    exact (congrArg Multiplicative.toAdd h3).symm
  obtain ⟨k, hxX, hx3, hxc⟩ := exists_mem_L₁Of_cube hlL' hlV2 hl3 hlc h2V hCL

  have hidx : (V₂.subgroupOf V).index = 2 := by
    have h1 := Subgroup.card_mul_index (V₂.subgroupOf V)
    rw [show Nat.card (V₂.subgroupOf V) = 4 by
      rw [← hc2]; exact Nat.card_congr (subgroupOfEquivOfLe h2V).toEquiv, hV8] at h1
    omega
  have hker : IsPGroup 2 ↥(L ⊓ centralizer (V₂ : Set G)) := by
    refine isPGroup_two_of_forall' fun x hx => ?_
    have hxN := hLV hx.1
    have hxc : ∀ w ∈ V₂, x * w = w * x := fun w hw => ((mem_centralizer_iff.1 hx.2) w hw).symm
    have hxsq : x ^ 2 ∈ L ⊓ centralizer (V : Set G) := by
      refine mem_inf.2 ⟨pow_mem hx.1 2, mem_centralizer_iff.2 fun v hv => ?_⟩
      have hv' : x * v * x⁻¹ ∈ V := (mem_normalizer_iff.1 hxN v).1 hv

      have hiff : x * v * x⁻¹ ∈ V₂ ↔ v ∈ V₂ := by
        constructor
        · intro h
          have h1 : x * (x * v * x⁻¹) = (x * v * x⁻¹) * x := hxc _ h
          have h2 : x * v * x⁻¹ = v := by
            have h3 : x * (x * v * x⁻¹) = x * v := by rw [h1]; group
            calc x * v * x⁻¹ = x⁻¹ * (x * (x * v * x⁻¹)) := by group
              _ = x⁻¹ * (x * v) := by rw [h3]
              _ = v := by group
          rwa [h2] at h
        · intro h
          rw [hxc v h, mul_inv_cancel_right]
          exact h

      have hu : x * v * x⁻¹ * v⁻¹ ∈ V₂ := by
        have h1 := Subgroup.mul_mem_iff_of_index_two hidx (a := ⟨x * v * x⁻¹, hv'⟩)
          (b := ⟨v⁻¹, inv_mem hv⟩)
        simp only [mem_subgroupOf] at h1
        refine h1.2 ⟨fun h => ?_, fun h => ?_⟩
        · exact inv_mem (hiff.1 h)
        · exact hiff.2 (by simpa using inv_mem h)
      obtain ⟨u, hu', huv⟩ : ∃ u ∈ V₂, x * v * x⁻¹ = u * v := ⟨_, hu, by group⟩
      have hu2 : u * u = 1 := hsq u (h2V hu')
      have hxu : x * u * x⁻¹ = u := by rw [hxc u hu', mul_inv_cancel_right]
      have key : x ^ 2 * v * (x ^ 2)⁻¹ = v := by
        calc x ^ 2 * v * (x ^ 2)⁻¹ = x * (x * v * x⁻¹) * x⁻¹ := by rw [pow_two]; group
          _ = x * (u * v) * x⁻¹ := by rw [huv]
          _ = (x * u * x⁻¹) * (x * v * x⁻¹) := by group
          _ = u * (u * v) := by rw [hxu, huv]
          _ = v := by rw [← mul_assoc, hu2, one_mul]
      calc v * x ^ 2 = x ^ 2 * v * (x ^ 2)⁻¹ * x ^ 2 := by rw [key]
        _ = x ^ 2 * v := by group
    obtain ⟨k, hk⟩ := exists_two_pow_eq_one hCL hxsq
    exact ⟨k + 1, by rw [pow_succ', pow_mul, hk]⟩

  obtain ⟨hXL, hXN, hXT, hXres⟩ := X_facts_L₂ (L := L) hTL hT2
  have hV3eq : ∀ V₃ : Subgroup G, V₃ ≤ V → Nat.card V₃ = 8 → V₃ = V := fun V₃ h3V hc3 =>
    Subgroup.eq_of_le_of_card_ge h3V (by rw [hc3, hV8])

  have hA5 : IsEmpty (↥(autOn L V) ≃* ↥(alternatingGroup (Fin 5))) :=
    ⟨fun e => not_five_dvd_card_autOn hL3 hV.2.2.1 (by
      rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]; decide)⟩
  refine (core15_of_F4 h1332 hH hV hzv hV2 (h13314 G T L V V₂ hH hV hzv hV2 hA5) hXL hXN hXT
    hXres ⟨_, hxX, hx3, hxc⟩ (hker.to_le (inf_le_inf_right _ hXL)) ?_ ?_).stmt hI₂ ?_
  · intro h
    exact hxc (Subgroup.centralizer_le h2V (hZC (h hxX)))
  · intro V₃ _ h3V _ hc3
    rw [hV3eq V₃ h3V hc3, inf_eq_left.2 hLV, sup_eq_right.2 hXL]
  · intro _ V₃ _ h3V _ hc3 c hc v _
    rw [hV3eq V₃ h3V hc3] at hc
    have hcv : v * c = c * v := (mem_centralizer_iff.1 hc.2) v ‹_›
    rw [commutatorElement_def, show v * c * v⁻¹ * c⁻¹ = (v * c) * (c * v)⁻¹ by group, hcv,
      mul_inv_cancel]
    exact one_mem _

end CFSG.Quasithin.H13.U3
