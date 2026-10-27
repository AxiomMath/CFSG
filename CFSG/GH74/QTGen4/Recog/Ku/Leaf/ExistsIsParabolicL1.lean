module

public import CFSG.GH74.QTGen4.Recog.Ku.HGlueC
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Quasithin.Background.FFC6P
public import CFSG.Quasithin.Recognition.HSTypeZQ
public import Certificates.Data.A5

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.GH74.QTGen4.Ku

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13 CFSG.Quasithin.HSType
  CFSG.Quasithin.L34Amalgam
open scoped IsMulCommutative

variable {G : Type} [Group G]

namespace ParL1

@[expose] def a₀ : Equiv.Perm (Fin 5) := Equiv.swap 0 1 * Equiv.swap 2 3

@[expose] def b₀ : Equiv.Perm (Fin 5) := Equiv.swap 1 2 * Equiv.swap 2 4

theorem a₀_mul_self : a₀ * a₀ = 1 := by decide

theorem b₀_pow_three : b₀ ^ 3 = 1 := by decide

theorem a₀_mul_b₀_pow_five : (a₀ * b₀) ^ 5 = 1 := by decide

theorem b₀_ne_one : b₀ ≠ 1 := by decide

theorem a₀_mem : a₀ ∈ alternatingGroup (Fin 5) :=
  Equiv.Perm.mem_alternatingGroup.mpr (by decide)

theorem b₀_mem : b₀ ∈ alternatingGroup (Fin 5) :=
  Equiv.Perm.mem_alternatingGroup.mpr (by decide)

@[expose] def step (l : List (Equiv.Perm (Fin 5))) : List (Equiv.Perm (Fin 5)) :=
  (l ++ l.map (a₀ * ·) ++ l.map (b₀ * ·)).dedup

theorem mem_closure_step {l : List (Equiv.Perm (Fin 5))}
    (hl : ∀ σ ∈ l, σ ∈ Subgroup.closure {a₀, b₀}) :
    ∀ σ ∈ step l, σ ∈ Subgroup.closure {a₀, b₀} := by
  intro σ hσ
  unfold step at hσ
  rw [List.mem_dedup, List.mem_append, List.mem_append] at hσ
  rcases hσ with (h | h) | h
  · exact hl σ h
  · obtain ⟨τ, hτ, rfl⟩ := List.mem_map.mp h
    exact Subgroup.mul_mem _ (Subgroup.subset_closure (Set.mem_insert _ _)) (hl τ hτ)
  · obtain ⟨τ, hτ, rfl⟩ := List.mem_map.mp h
    exact Subgroup.mul_mem _ (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)) (hl τ hτ)

theorem mem_closure_iterate (n : ℕ) : ∀ σ ∈ step^[n] [1], σ ∈ Subgroup.closure {a₀, b₀} := by
  induction n with
  | zero =>
    intro σ hσ
    rw [Function.iterate_zero, id, List.mem_singleton] at hσ
    rw [hσ]
    exact Subgroup.one_mem _
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact mem_closure_step ih

theorem alt_mem_iterate :
    ∀ σ : Equiv.Perm (Fin 5), Equiv.Perm.sign σ = 1 → σ ∈ step^[12] [1] := by
  decide +kernel

theorem closure_a₀_b₀ : Subgroup.closure {a₀, b₀} = alternatingGroup (Fin 5) := by
  refine le_antisymm ?_ fun σ hσ => ?_
  · rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact a₀_mem
    · exact b₀_mem
  · exact mem_closure_iterate 12 σ (alt_mem_iterate σ (Equiv.Perm.mem_alternatingGroup.mp hσ))

end ParL1

namespace KuHyp

variable [Finite G] {T M H P : Subgroup G} {z : G}

theorem parL1_exists_complement_of_elemAbelian {F C : Subgroup G} (hF : IsElemAbelian 2 F)
    (hCF : C ≤ F) : ∃ K : Subgroup G, K ≤ F ∧ C ⊓ K = ⊥ ∧ C ⊔ K = F := by
  let _ : CommGroup ↥F := commGroupOfElemAbelian hF
  have hsq : ∀ v : ↥F, v ^ 2 = 1 := fun v => Subtype.ext (by
    rw [Subgroup.coe_pow, hF.2 (v : G) v.2, Subgroup.coe_one])
  obtain ⟨S, -, hSd, hSc⟩ := FFC.B59.exists_complement_in (V := ↥F) hsq
    (C := C.subgroupOf F) (F := ⊤) le_top
  refine ⟨S.map F.subtype, Subgroup.map_subtype_le S, ?_, ?_⟩
  · refine (Subgroup.eq_bot_iff_forall _).mpr fun x hx => ?_
    obtain ⟨hxC, hxK⟩ := Subgroup.mem_inf.mp hx
    obtain ⟨y, hyS, rfl⟩ := Subgroup.mem_map.mp hxK
    have hyC : y ∈ C.subgroupOf F := Subgroup.mem_subgroupOf.mpr hxC
    have hy : y ∈ S ⊓ C.subgroupOf F := ⟨hyS, hyC⟩
    rw [hSd, Subgroup.mem_bot] at hy
    simp [hy]
  · apply le_antisymm
    · exact sup_le hCF (Subgroup.map_subtype_le S)
    · intro x hx
      have hy : (⟨x, hx⟩ : ↥F) ∈ S ⊔ C.subgroupOf F := by
        rw [hSc]; exact Subgroup.mem_top _
      obtain ⟨s, hs, c, hc, hsc⟩ := Subgroup.mem_sup.mp hy
      have hsK : (s : G) ∈ S.map F.subtype := Subgroup.mem_map.mpr ⟨s, hs, rfl⟩
      have hcC : (c : G) ∈ C := Subgroup.mem_subgroupOf.mp hc
      have hx' : (s : G) * (c : G) = x := by rw [← Subgroup.coe_mul, hsc]
      have h1 : (s : G) ∈ C ⊔ S.map F.subtype :=
        (le_sup_right : S.map F.subtype ≤ C ⊔ S.map F.subtype) hsK
      have h2 : (c : G) ∈ C ⊔ S.map F.subtype :=
        (le_sup_left : C ≤ C ⊔ S.map F.subtype) hcC
      rw [← hx']
      exact Subgroup.mul_mem _ h1 h2

theorem parL1_exists_complement_kuR [KuLeaf LeafCardKuA] [KuLeaf LeafIsMulCommutativeKuA]
    [KuLeaf LeafEqKuAOfElemAbelian] [KuLeaf LeafTInfCentralizerKuWLeKuA] [KuLeaf LeafKuV2LeKuW]
    (h : KuHyp G T M H P z) :
    ∃ K : Subgroup G, K ≤ kuR T M ∧ pCoreOf 2 M ⊓ K = ⊥ ∧ pCoreOf 2 M ⊔ K = kuR T M := by
  have hV2E : kuV2 T M ≤ kuA P H := by
    rw [← h.kuA_inf_pCore_M]; exact inf_le_left
  obtain ⟨K, hKE, hKd, hKs⟩ :=
    parL1_exists_complement_of_elemAbelian h.isElemAbelian_kuA hV2E
  have hER : kuA P H ≤ kuR T M := h.kuA_le_kuR
  refine ⟨K, hKE.trans hER, ?_, ?_⟩
  · refine (Subgroup.eq_bot_iff_forall _).mpr fun x hx => ?_
    obtain ⟨hxV, hxK⟩ := Subgroup.mem_inf.mp hx
    have hx2 : x ∈ kuA P H ⊓ pCoreOf 2 M := ⟨hKE hxK, hxV⟩
    rw [h.kuA_inf_pCore_M] at hx2
    have hx3 : x ∈ kuV2 T M ⊓ K := ⟨hx2, hxK⟩
    rw [hKd, Subgroup.mem_bot] at hx3
    exact hx3
  · refine le_antisymm (sup_le h.pCore_le_kuR (hKE.trans hER)) ?_
    rw [← h.E_sup_pCore ⟨hER, h.isElemAbelian_kuA, h.card_kuA, h.kuA_inf_pCore_M⟩]
    refine sup_le ?_ le_sup_left
    rw [← hKs]
    exact sup_le (inf_le_left.trans le_sup_left) le_sup_right

theorem parL1_exists_complement_L1 [KuLeaf LeafCardKuA] [KuLeaf LeafIsMulCommutativeKuA]
    [KuLeaf LeafEqKuAOfElemAbelian] [KuLeaf LeafTInfCentralizerKuWLeKuA] [KuLeaf LeafKuV2LeKuW]
    (h : KuHyp G T M H P z) :
    ∃ C : Subgroup G, C ≤ oTwoUpper M ∧ pCoreOf 2 M ⊓ C = ⊥ ∧ Nat.card C = 60 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨K, hKR, hKd, hKs⟩ := h.parL1_exists_complement_kuR
  have hVL : pCoreOf 2 M ≤ oTwoUpper M := h.pCore_le_oTwoUpper
  have hRL : kuR T M ≤ oTwoUpper M := inf_le_right
  have hKL : K ≤ oTwoUpper M := hKR.trans hRL
  have hVn : ((pCoreOf 2 M).subgroupOf (oTwoUpper M)).Normal := ⟨fun n hn x => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have h1 := (Subgroup.mem_normalizer_iff.mp (h.oTwoUpper_le_normalizer_V x.2) (n : G)).mp hn
    simpa using h1⟩
  have hcomm : ∀ a ∈ pCoreOf 2 M, ∀ b ∈ pCoreOf 2 M, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (h.vElem.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hVc : IsMulCommutative ↥((pCoreOf 2 M).subgroupOf (oTwoUpper M)) := ⟨⟨fun a b =>
    Subtype.ext (Subtype.ext (hcomm _ (Subgroup.mem_subgroupOf.mp a.2) _
      (Subgroup.mem_subgroupOf.mp b.2)))⟩⟩
  have hVcard : Nat.card ↥((pCoreOf 2 M).subgroupOf (oTwoUpper M)) = 16 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVL).toEquiv, h.vCard]
  have hRc : Nat.card ↥((kuR T M).subgroupOf (oTwoUpper M)) = 64 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRL).toEquiv, h.card_kuR]
  have hVp : IsPGroup 2 ↥((pCoreOf 2 M).subgroupOf (oTwoUpper M)) :=
    IsPGroup.of_card (n := 4) (by rw [hVcard]; norm_num)
  have hRp : IsPGroup 2 ↥((kuR T M).subgroupOf (oTwoUpper M)) :=
    IsPGroup.of_card (n := 6) (by rw [hRc]; norm_num)
  have hRidx : ¬ 2 ∣ ((kuR T M).subgroupOf (oTwoUpper M)).index := by
    have h1 := ((kuR T M).subgroupOf (oTwoUpper M)).card_mul_index
    rw [hRc, h.card_oTwoUpper] at h1
    have h15 : ((kuR T M).subgroupOf (oTwoUpper M)).index = 15 := by omega
    rw [h15]
    decide
  let S : Sylow 2 ↥(oTwoUpper M) := hRp.toSylow hRidx
  have hS : (S : Subgroup ↥(oTwoUpper M)) = (kuR T M).subgroupOf (oTwoUpper M) := rfl
  have hd1 : (pCoreOf 2 M).subgroupOf (oTwoUpper M) ⊓ K.subgroupOf (oTwoUpper M) = ⊥ := by
    refine (Subgroup.eq_bot_iff_forall _).mpr fun x hx => ?_
    obtain ⟨h1, h2⟩ := Subgroup.mem_inf.mp hx
    have h3 : (x : G) ∈ pCoreOf 2 M ⊓ K :=
      Subgroup.mem_inf.mpr ⟨Subgroup.mem_subgroupOf.mp h1, Subgroup.mem_subgroupOf.mp h2⟩
    rw [hKd, Subgroup.mem_bot] at h3
    exact Subtype.ext h3
  have hsup : (pCoreOf 2 M).subgroupOf (oTwoUpper M) ⊔ K.subgroupOf (oTwoUpper M) =
      (S : Subgroup ↥(oTwoUpper M)) := by
    rw [hS, ← Subgroup.subgroupOf_sup hVL hKL, hKs]
  have hKS : K.subgroupOf (oTwoUpper M) ≤ (S : Subgroup ↥(oTwoUpper M)) := by
    rw [hS]
    intro x hx
    exact Subgroup.mem_subgroupOf.mpr (hKR (Subgroup.mem_subgroupOf.mp hx))
  obtain ⟨Kc, hK1, hK2⟩ := (gaschutz (G := ↥(oTwoUpper M)) hVp S).mpr
    ⟨K.subgroupOf (oTwoUpper M), hKS, hd1, hsup⟩
  refine ⟨Kc.map (oTwoUpper M).subtype, Subgroup.map_subtype_le Kc, ?_, ?_⟩
  · refine (Subgroup.eq_bot_iff_forall _).mpr fun x hx => ?_
    obtain ⟨hxV, hxC⟩ := Subgroup.mem_inf.mp hx
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hxC
    have hkV : k ∈ (pCoreOf 2 M).subgroupOf (oTwoUpper M) := Subgroup.mem_subgroupOf.mpr hxV
    have hk1 : k ∈ (pCoreOf 2 M).subgroupOf (oTwoUpper M) ⊓ Kc := ⟨hkV, hk⟩
    rw [hK1, Subgroup.mem_bot] at hk1
    simp [hk1]
  · have hN : Kc ≤ Subgroup.normalizer
        ((pCoreOf 2 M).subgroupOf (oTwoUpper M) : Set ↥(oTwoUpper M)) := by
      rw [Subgroup.normalizer_eq_top]; exact le_top
    have hp := card_sup_mul_card_inf_of_le_normalizer hN
    rw [sup_comm, hK2, inf_comm, hK1, Subgroup.card_top, Subgroup.card_bot, mul_one,
      h.card_oTwoUpper, hVcard] at hp
    rw [Subgroup.card_map_of_injective (oTwoUpper M).subtype_injective]
    omega

theorem parL1_exists_isParabolic [KuLeaf LeafCardKuA] [KuLeaf LeafIsMulCommutativeKuA]
    [KuLeaf LeafEqKuAOfElemAbelian] [KuLeaf LeafTInfCentralizerKuWLeKuA] [KuLeaf LeafKuV2LeKuW]
    (h : KuHyp G T M H P z) :
    ∃ a b : G, IsParabolic (oTwoUpper M) (pCoreOf 2 M) a b := by
  obtain ⟨C, hCL, hVC, hCc⟩ := h.parL1_exists_complement_L1
  obtain ⟨φ, -, hker⟩ := h.mQuot
  have hCM : C ≤ M := hCL.trans (oTwoUpper_le M)
  set ψ : ↥C →* Equiv.Perm (Fin 5) := φ.comp (Subgroup.inclusion hCM) with hψdef
  have hψ : ∀ c : ↥C, ψ c = φ ⟨c, hCM c.2⟩ := fun c => rfl
  have hinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro c hc
    rw [hψ] at hc
    have hcV : (c : G) ∈ pCoreOf 2 M := by
      have h1 : (⟨c, hCM c.2⟩ : ↥M) ∈ φ.ker := hc
      rw [hker, Subgroup.mem_subgroupOf] at h1
      exact h1
    have hcVC : (c : G) ∈ pCoreOf 2 M ⊓ C := ⟨hcV, c.2⟩
    rw [hVC, Subgroup.mem_bot] at hcVC
    exact Subtype.ext hcVC
  have halt : ∀ c : ↥C, ψ c ∈ alternatingGroup (Fin 5) := by
    intro c
    obtain ⟨w, hw, hwx⟩ := Subgroup.mem_map.mp (oTwoUpper_le_map_comap φ (hCL c.2))
    have hwe : w = ⟨c, hCM c.2⟩ := Subtype.ext hwx
    rw [hψ, ← hwe]
    exact hw
  have hrange : ψ.range = alternatingGroup (Fin 5) := by
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro _ ⟨c, rfl⟩
      exact halt c
    · rw [card_alt_fin5, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, hCc]
  obtain ⟨a, ha⟩ := MonoidHom.mem_range.mp
    (show ParL1.a₀ ∈ ψ.range by rw [hrange]; exact ParL1.a₀_mem)
  obtain ⟨b, hb⟩ := MonoidHom.mem_range.mp
    (show ParL1.b₀ ∈ ψ.range by rw [hrange]; exact ParL1.b₀_mem)
  have ha2 : a * a = 1 := hinj (by rw [map_mul, ha, ParL1.a₀_mul_self, map_one])
  have hb3 : b ^ 3 = 1 := hinj (by rw [map_pow, hb, ParL1.b₀_pow_three, map_one])
  have hab5 : (a * b) ^ 5 = 1 :=
    hinj (by rw [map_pow, map_mul, ha, hb, ParL1.a₀_mul_b₀_pow_five, map_one])
  have hcl : Subgroup.closure {(a : G), (b : G)} = C := by
    refine le_antisymm ?_ fun c hc => ?_
    · rw [Subgroup.closure_le]
      rintro _ (rfl | rfl)
      · exact a.2
      · exact b.2
    · have hmem : ψ ⟨c, hc⟩ ∈ (Subgroup.closure {a, b}).map ψ := by
        rw [MonoidHom.map_closure, Set.image_pair, ha, hb, ParL1.closure_a₀_b₀, ← hrange]
        exact MonoidHom.mem_range.mpr ⟨⟨c, hc⟩, rfl⟩
      obtain ⟨d, hd, hdc⟩ := hmem
      rw [hinj hdc] at hd
      have hmap : (Subgroup.closure {a, b}).map C.subtype =
          Subgroup.closure {(a : G), (b : G)} := by
        rw [MonoidHom.map_closure, Set.image_pair, Subgroup.coe_subtype]
      rw [← hmap]
      exact ⟨⟨c, hc⟩, hd, rfl⟩
  have hb1 : (b : G) ≠ 1 := by
    intro e
    have hb1' : b = 1 := Subtype.ext e
    exact ParL1.b₀_ne_one (by rw [← hb, hb1', map_one])
  have hbL : (b : G) ∈ oTwoUpper M := hCL b.2
  have hb3G : (b : G) ^ 3 = 1 := by rw [← Subgroup.coe_pow, hb3, Subgroup.coe_one]
  have hbo : orderOf (b : G) = 3 := by
    have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    exact orderOf_eq_prime hb3G hb1
  have fpf : ∀ e ∈ pCoreOf 2 M, (b : G) * e = e * (b : G) → e = 1 := fun e he hbe =>
    h.fpf_of_order_three hbL hbo he (by rw [hbe, mul_inv_cancel_right])
  refine ⟨(a : G), (b : G),
    { le := h.pCore_le_oTwoUpper
      normal := fun x hx e he =>
        (Subgroup.mem_normalizer_iff.mp (h.oTwoUpper_le_normalizer_V hx) e).mp he
      mul_self := fun e he => by rw [← sq]; exact h.vElem.2 e he
      card_E := h.vCard
      card := h.card_oTwoUpper
      mem_a := hCL a.2
      mem_b := hbL
      inf := by rw [hcl]; exact hVC
      card_C := by rw [hcl]; exact hCc
      ha := congrArg Subtype.val ha2
      hb := hb3G
      hab := by rw [← Subgroup.coe_mul, ← Subgroup.coe_pow, hab5, Subgroup.coe_one]
      fpf := fpf }⟩

end KuHyp

theorem leafExistsIsParabolicL1
    [KuLeaf LeafCardKuA] [KuLeaf LeafIsMulCommutativeKuA] [KuLeaf LeafEqKuAOfElemAbelian]
    [KuLeaf LeafTInfCentralizerKuWLeKuA] [KuLeaf LeafKuV2LeKuW]
    : LeafExistsIsParabolicL1 := by
  intro G _ _ T M H P z h
  exact h.parL1_exists_isParabolic

end CFSG.GH74.QTGen4.Ku
