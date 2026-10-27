module

public import CFSG.GH74.QTGen4.Recog.Ku.Parabolics
public import CFSG.Quasithin.Recognition.HSTypeZQ
public import CFSG.Quasithin.Background.FFC6P

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.GH74.QTGen4.Ku

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13 CFSG.Quasithin.HSType
  CFSG.Quasithin.L34Amalgam
open scoped IsMulCommutative

variable {G : Type} [Group G]

namespace KuA6Model

variable {E W V2 N : Subgroup G} {z : G}

theorem comm_mem (Ψ : KuA6Model E W V2 N z) {x y : G} (hx : x ∈ E) (hy : y ∈ E) :
    x * y = y * x := by
  obtain ⟨u, rfl⟩ := Ψ.surj x hx
  obtain ⟨v, rfl⟩ := Ψ.surj y hy
  rw [← Ψ.add, ← Ψ.add, add_comm]

theorem elem_abelian (Ψ : KuA6Model E W V2 N z) : IsElemAbelian 2 E := by
  have hz : ∀ x : ZMod 2, x + x = 0 := by decide
  have hadd : ∀ u : SpV, u + u = 0 := fun u => funext fun i => hz (u i)
  refine ⟨⟨⟨fun a b => Subtype.ext (Ψ.comm_mem a.2 b.2)⟩⟩, fun x hx => ?_⟩
  obtain ⟨u, rfl⟩ := Ψ.surj x hx
  rw [sq, ← Ψ.add, hadd, Ψ.Φ_zero]

end KuA6Model

namespace KuHyp

variable [Finite G] {T M H P : Subgroup G} {z : G}

theorem exists_complement_pCore (h : KuHyp G T M H P z) :
    ∃ K : Subgroup G, K ≤ pCoreOf 2 M ∧ kuV2 T M ⊓ K = ⊥ ∧ kuV2 T M ⊔ K = pCoreOf 2 M := by
  have hV : IsElemAbelian 2 (pCoreOf 2 M) := h.vElem
  let _ : CommGroup ↥(pCoreOf 2 M) := commGroupOfElemAbelian hV
  have hsq : ∀ v : ↥(pCoreOf 2 M), v ^ 2 = 1 := fun v => Subtype.ext (by
    rw [Subgroup.coe_pow, hV.2 (v : G) v.2, Subgroup.coe_one])
  obtain ⟨S, -, hSd, hSc⟩ := FFC.B59.exists_complement_in (V := ↥(pCoreOf 2 M)) hsq
    (C := (kuV2 T M).subgroupOf (pCoreOf 2 M)) (F := ⊤) le_top
  refine ⟨S.map (pCoreOf 2 M).subtype, Subgroup.map_subtype_le S, ?_, ?_⟩
  · refine (Subgroup.eq_bot_iff_forall _).mpr fun x hx => ?_
    obtain ⟨hxV, hxK⟩ := Subgroup.mem_inf.mp hx
    obtain ⟨y, hyS, rfl⟩ := Subgroup.mem_map.mp hxK
    have hyC : y ∈ (kuV2 T M).subgroupOf (pCoreOf 2 M) := Subgroup.mem_subgroupOf.mpr hxV
    have hy : y ∈ S ⊓ (kuV2 T M).subgroupOf (pCoreOf 2 M) := ⟨hyS, hyC⟩
    rw [hSd, Subgroup.mem_bot] at hy
    simp [hy]
  · apply le_antisymm
    · exact sup_le inf_le_left (Subgroup.map_subtype_le S)
    · intro x hx
      have hy : (⟨x, hx⟩ : ↥(pCoreOf 2 M)) ∈ S ⊔ (kuV2 T M).subgroupOf (pCoreOf 2 M) := by
        rw [hSc]; exact Subgroup.mem_top _
      obtain ⟨s, hs, c, hc, hsc⟩ := Subgroup.mem_sup.mp hy
      have hsK : (s : G) ∈ S.map (pCoreOf 2 M).subtype := Subgroup.mem_map.mpr ⟨s, hs, rfl⟩
      have hcV : (c : G) ∈ kuV2 T M := Subgroup.mem_subgroupOf.mp hc
      have hx' : (s : G) * (c : G) = x := by rw [← Subgroup.coe_mul, hsc]
      have h1 : (s : G) ∈ kuV2 T M ⊔ S.map (pCoreOf 2 M).subtype :=
        (le_sup_right : S.map (pCoreOf 2 M).subtype ≤ kuV2 T M ⊔ S.map (pCoreOf 2 M).subtype) hsK
      have h2 : (c : G) ∈ kuV2 T M ⊔ S.map (pCoreOf 2 M).subtype :=
        (le_sup_left : kuV2 T M ≤ kuV2 T M ⊔ S.map (pCoreOf 2 M).subtype) hcV
      rw [← hx']
      exact Subgroup.mul_mem _ h1 h2

theorem exists_complement_kuA [KuLeaf LeafIsMulCommutativeKuA] [KuLeaf LeafEqKuAOfElemAbelian]
    [KuLeaf LeafTInfCentralizerKuWLeKuA] [KuLeaf LeafKuV2LeKuW]
    (h : KuHyp G T M H P z)
    (Ψ : KuA6Model (kuA P H) (kuW P H) (kuV2 T M) (kuN P H) z) :
    ∃ K : Subgroup G, K ≤ pCoreOf 2 M ∧ kuA P H ⊓ K = ⊥ ∧ kuA P H ⊔ K = kuR T M := by
  obtain ⟨K, hKV, hKd, hKs⟩ := h.exists_complement_pCore
  have hV2A : kuV2 T M ≤ kuA P H := by
    rw [← h.kuA_inf_pCore_M]; exact inf_le_left
  refine ⟨K, hKV, ?_, ?_⟩
  · refine (Subgroup.eq_bot_iff_forall _).mpr fun x hx => ?_
    obtain ⟨hxE, hxK⟩ := Subgroup.mem_inf.mp hx
    have hxV : x ∈ kuA P H ⊓ pCoreOf 2 M := Subgroup.mem_inf.mpr ⟨hxE, hKV hxK⟩
    rw [h.kuA_inf_pCore_M] at hxV
    have hx3 : x ∈ kuV2 T M ⊓ K := Subgroup.mem_inf.mpr ⟨hxV, hxK⟩
    rw [hKd, Subgroup.mem_bot] at hx3
    exact hx3
  · apply le_antisymm
    · exact sup_le h.kuA_le_kuR (hKV.trans h.pCore_le_kuR)
    · have hE := h.E_sup_pCore ⟨h.kuA_le_kuR, Ψ.elem_abelian, Ψ.card_E, h.kuA_inf_pCore_M⟩
      rw [← hE]
      exact sup_le le_sup_left (by rw [← hKs]; exact sup_le (hV2A.trans le_sup_left) le_sup_right)

theorem exists_complement_L2 [KuLeaf LeafIsMulCommutativeKuA] [KuLeaf LeafEqKuAOfElemAbelian]
    [KuLeaf LeafTInfCentralizerKuWLeKuA] [KuLeaf LeafKuV2LeKuW]
    (h : KuHyp G T M H P z)
    (Ψ : KuA6Model (kuA P H) (kuW P H) (kuV2 T M) (kuN P H) z) :
    ∃ C : Subgroup G, C ≤ Ψ.L2 ∧ kuA P H ⊓ C = ⊥ ∧ Nat.card C = 60 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨K, hKV, hKd, hKs⟩ := h.exists_complement_kuA Ψ
  have hEL : kuA P H ≤ Ψ.L2 := kuA_le_pre Ψ lamS
  have hRL : kuR T M ≤ Ψ.L2 := by
    rw [h.kuR_eq_pre_kleinS Ψ]; exact Ψ.pre_mono kleinS_le_lamS
  have hKR : K ≤ kuR T M := hKV.trans h.pCore_le_kuR
  have hKL : K ≤ Ψ.L2 := hKR.trans hRL
  have hEn : ((kuA P H).subgroupOf Ψ.L2).Normal := ⟨fun n hn x => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have h1 := (Subgroup.mem_normalizer_iff.mp (pre_le_kuN Ψ lamS x.2) (n : G)).mp hn
    simpa using h1⟩
  have hEc : IsMulCommutative ↥((kuA P H).subgroupOf Ψ.L2) := ⟨⟨fun a b =>
    Subtype.ext (Subtype.ext (Ψ.comm_mem (Subgroup.mem_subgroupOf.mp a.2)
      (Subgroup.mem_subgroupOf.mp b.2)))⟩⟩
  have hVc : Nat.card ↥((kuA P H).subgroupOf Ψ.L2) = 16 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEL).toEquiv, Ψ.card_E]
  have hRc : Nat.card ↥((kuR T M).subgroupOf Ψ.L2) = 64 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRL).toEquiv, h.card_kuR]
  have hVp : IsPGroup 2 ↥((kuA P H).subgroupOf Ψ.L2) :=
    IsPGroup.of_card (n := 4) (by rw [hVc]; norm_num)
  have hRp : IsPGroup 2 ↥((kuR T M).subgroupOf Ψ.L2) :=
    IsPGroup.of_card (n := 6) (by rw [hRc]; norm_num)
  have hRidx : ¬ 2 ∣ ((kuR T M).subgroupOf Ψ.L2).index := by
    have h1 := ((kuR T M).subgroupOf Ψ.L2).card_mul_index
    rw [hRc, h.card_L2 Ψ] at h1
    have h15 : ((kuR T M).subgroupOf Ψ.L2).index = 15 := by omega
    rw [h15]
    decide
  let S : Sylow 2 ↥Ψ.L2 := hRp.toSylow hRidx
  have hS : (S : Subgroup ↥Ψ.L2) = (kuR T M).subgroupOf Ψ.L2 := rfl
  have hd1 : (kuA P H).subgroupOf Ψ.L2 ⊓ K.subgroupOf Ψ.L2 = ⊥ := by
    refine (Subgroup.eq_bot_iff_forall _).mpr fun x hx => ?_
    obtain ⟨h1, h2⟩ := Subgroup.mem_inf.mp hx
    have h3 : (x : G) ∈ kuA P H ⊓ K :=
      Subgroup.mem_inf.mpr ⟨Subgroup.mem_subgroupOf.mp h1, Subgroup.mem_subgroupOf.mp h2⟩
    rw [hKd, Subgroup.mem_bot] at h3
    exact Subtype.ext h3
  have hsup : (kuA P H).subgroupOf Ψ.L2 ⊔ K.subgroupOf Ψ.L2 = (S : Subgroup ↥Ψ.L2) := by
    rw [hS, ← Subgroup.subgroupOf_sup hEL hKL, hKs]
  have hKS : K.subgroupOf Ψ.L2 ≤ (S : Subgroup ↥Ψ.L2) := by
    rw [hS]
    intro x hx
    exact Subgroup.mem_subgroupOf.mpr (hKR (Subgroup.mem_subgroupOf.mp hx))
  obtain ⟨Kc, hK1, hK2⟩ := (gaschutz (G := ↥Ψ.L2) hVp S).mpr
    ⟨K.subgroupOf Ψ.L2, hKS, hd1, hsup⟩
  refine ⟨Kc.map Ψ.L2.subtype, Subgroup.map_subtype_le Kc, ?_, ?_⟩
  · refine (Subgroup.eq_bot_iff_forall _).mpr fun x hx => ?_
    obtain ⟨hxE, hxC⟩ := Subgroup.mem_inf.mp hx
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hxC
    have hkE : k ∈ (kuA P H).subgroupOf Ψ.L2 := Subgroup.mem_subgroupOf.mpr hxE
    have hk1 : k ∈ (kuA P H).subgroupOf Ψ.L2 ⊓ Kc := ⟨hkE, hk⟩
    rw [hK1, Subgroup.mem_bot] at hk1
    simp [hk1]
  · have hN : Kc ≤ Subgroup.normalizer ((kuA P H).subgroupOf Ψ.L2 : Set ↥Ψ.L2) := by
      rw [Subgroup.normalizer_eq_top]; exact le_top
    have hp := card_sup_mul_card_inf_of_le_normalizer hN
    rw [sup_comm, hK2, inf_comm, hK1, Subgroup.card_top, Subgroup.card_bot, mul_one,
      h.card_L2 Ψ, hVc] at hp
    rw [Subgroup.card_map_of_injective Ψ.L2.subtype_injective]
    omega

theorem exists_isParabolic_L2 [KuLeaf LeafIsMulCommutativeKuA] [KuLeaf LeafEqKuAOfElemAbelian]
    [KuLeaf LeafTInfCentralizerKuWLeKuA] [KuLeaf LeafKuV2LeKuW]
    (h : KuHyp G T M H P z)
    (Ψ : KuA6Model (kuA P H) (kuW P H) (kuV2 T M) (kuN P H) z) :
    ∃ a b : G, IsParabolic Ψ.L2 (kuA P H) a b := by
  obtain ⟨C, hCL, hBC, hCc⟩ := h.exists_complement_L2 Ψ
  have hCN : C ≤ kuN P H := hCL.trans (pre_le_kuN Ψ lamS)
  set πC : ↥C →* Equiv.Perm (Fin 6) := Ψ.π.comp (Subgroup.inclusion hCN) with hπCdef
  have hπC : ∀ c : ↥C, πC c = Ψ.π ⟨c, hCN c.2⟩ := fun c => rfl
  have hinj : Function.Injective πC := by
    rw [injective_iff_map_eq_one]
    intro c hc
    rw [hπC] at hc
    have hcE : (c : G) ∈ kuA P H := (Ψ.ker ⟨c, hCN c.2⟩).mp hc
    have hcEC : (c : G) ∈ kuA P H ⊓ C := ⟨hcE, c.2⟩
    rw [hBC, Subgroup.mem_bot] at hcEC
    exact Subtype.ext hcEC
  have hrange : πC.range = lamS := by
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · intro x hx
      obtain ⟨c, rfl⟩ := MonoidHom.mem_range.mp hx
      rw [hπC]
      obtain ⟨_, hmem⟩ := (Ψ.mem_pre_iff lamS).mp (hCL c.2)
      exact hmem
    · rw [card_lamS, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, hCc]
  obtain ⟨a, ha⟩ := MonoidHom.mem_range.mp (show αS ∈ πC.range by rw [hrange]; exact αS_mem)
  obtain ⟨b, hb⟩ := MonoidHom.mem_range.mp (show βS ∈ πC.range by rw [hrange]; exact βS_mem)
  have ha2 : a * a = 1 := hinj (by rw [map_mul, ha, αS_mul_self, map_one])
  have hb3 : b ^ 3 = 1 := hinj (by rw [map_pow, hb, βS_pow_three, map_one])
  have hab5 : (a * b) ^ 5 = 1 := hinj (by rw [map_pow, map_mul, ha, hb, αS_βS_pow_five, map_one])
  have hcl : Subgroup.closure {(a : G), (b : G)} = C := by
    refine le_antisymm ?_ fun c hc => ?_
    · rw [Subgroup.closure_le]
      rintro _ (rfl | rfl)
      · exact a.2
      · exact b.2
    · have hmem : πC ⟨c, hc⟩ ∈ (Subgroup.closure {a, b}).map πC := by
        rw [MonoidHom.map_closure, Set.image_pair, ha, hb, closure_αS_βS, ← hrange]
        exact MonoidHom.mem_range.mpr ⟨⟨c, hc⟩, rfl⟩
      obtain ⟨d, hd, hdc⟩ := hmem
      rw [hinj hdc] at hd
      have hmap : (Subgroup.closure {a, b}).map C.subtype =
          Subgroup.closure {(a : G), (b : G)} := by
        rw [MonoidHom.map_closure, Set.image_pair, Subgroup.coe_subtype]
      rw [← hmap]
      exact ⟨⟨c, hc⟩, hd, rfl⟩
  have hbN : (b : G) ∈ kuN P H := hCN b.2
  have hπb : Ψ.π ⟨(b : G), hbN⟩ = βS := by rw [← hb, hπC]
  have fpf : ∀ e ∈ kuA P H, (b : G) * e = e * (b : G) → e = 1 := by
    intro e he hbe
    obtain ⟨u, rfl⟩ := Ψ.surj e he
    have h1 : (b : G) * Ψ.Φ u * (b : G)⁻¹ = Ψ.Φ u := by rw [hbe, mul_inv_cancel_right]
    have h2 : Ψ.Φ (actS6 (Ψ.π ⟨(b : G), hbN⟩) u) = Ψ.Φ u := by
      rw [← Ψ.act]; exact h1
    rw [hπb] at h2
    have hu : u = 0 := eq_zero_of_actS6_βS u (Ψ.inj h2)
    rw [hu, Ψ.Φ_zero]
  refine ⟨(a : G), (b : G),
    { le := kuA_le_pre Ψ lamS
      normal := fun x hx e he => (Subgroup.mem_normalizer_iff.mp (pre_le_kuN Ψ lamS hx) e).mp he
      mul_self := fun e he => by rw [← sq]; exact Ψ.elem_abelian.2 e he
      card_E := Ψ.card_E
      card := h.card_L2 Ψ
      mem_a := hCL a.2
      mem_b := hCL b.2
      inf := by rw [hcl]; exact hBC
      card_C := by rw [hcl]; exact hCc
      ha := congrArg Subtype.val ha2
      hb := by rw [← Subgroup.coe_pow, hb3, Subgroup.coe_one]
      hab := by rw [← Subgroup.coe_mul, ← Subgroup.coe_pow, hab5, Subgroup.coe_one]
      fpf := fpf }⟩

end KuHyp

end CFSG.GH74.QTGen4.Ku
