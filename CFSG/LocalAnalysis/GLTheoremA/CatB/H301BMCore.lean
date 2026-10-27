module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H301BMCoreGen
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H301BMLocal
public import CFSG.Monster.B.Fischer.Fi22Order

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GLTheoremA.H301B

open CFSG.Open CFSG.Monster CFSG.Monster.Existence CFSG.Monster.Existence.Co1Bridge
  CFSG.HardMathSupport.Dickson.I271.TabMFive CFSG.Sporadic.Co1Schreier

open scoped Matrix

section Generic

variable {G K V : Type*} [Group G] [Finite G] [Group K]

private theorem map_inf_centralizer_of_le {C : Subgroup G} (N : Subgroup C) {H : Subgroup G}
    (hH : H ≤ C) : (N ⊓ Subgroup.centralizer (H.subgroupOf C : Set C)).map C.subtype =
      N.map C.subtype ⊓ Subgroup.centralizer (H : Set G) := by
  ext g
  constructor
  · rintro ⟨y, ⟨hyN, hyc⟩, rfl⟩
    exact ⟨⟨y, hyN, rfl⟩, Subgroup.mem_centralizer_iff.2 fun h hh => congrArg Subtype.val
      (Subgroup.mem_centralizer_iff.1 hyc ⟨h, hH hh⟩ (Subgroup.mem_subgroupOf.2 hh))⟩
  · rintro ⟨⟨y, hyN, rfl⟩, hyc⟩
    exact ⟨y, ⟨hyN, Subgroup.mem_centralizer_iff.2 fun h hh => Subtype.ext
      (Subgroup.mem_centralizer_iff.1 hyc h (Subgroup.mem_subgroupOf.1 hh))⟩, rfl⟩

private theorem extraspecial_of_quot {p r k : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hk : ∀ j, 0 < j → j < k → ¬ 2 ^ j ≡ 1 [MOD p]) (act : K → V → V) (v0 : V)
    (hfixB : ∀ F : Subgroup K, IsElemAbelian p F → Nat.card F = p ^ r → ∀ v : V,
      (∀ j ∈ F, act j v = v) → v = v0)
    (hfixH : ∀ F H : Subgroup K, IsElemAbelian p F → Nat.card F = p ^ r → H ≤ F →
      Nat.card H * p = Nat.card F → Nat.card {v : V // ∀ j ∈ H, act j v = v} ≤ 2 ^ k)
    {x : G} (hx2 : orderOf x = 2) {C : Subgroup G} (hC : ∀ g, g ∈ C ↔ g * x = x * g)
    {N : Subgroup C} [N.Normal] (hR : timmesfeldIsExtraspecial ↥(N.map C.subtype))
    (hcR : Subgroup.centralizer (N.map C.subtype : Set G) ≤ N.map C.subtype)
    (hN : IsPGroup 2 N)
    (hle : ∀ F T : Subgroup C, IsElemAbelian p F → Nat.card F = p ^ r → IsPGroup 2 T →
      F ≤ Subgroup.normalizer (T : Set C) → T ≤ N)
    (e : C ⧸ N ≃* K)
    (hbound : ∀ H : Subgroup C, Nat.card ↥(N ⊓ Subgroup.centralizer (H : Set C)) ≤
      2 * Nat.card {v : V // ∀ h ∈ H, act (e (QuotientGroup.mk h)) v = v})
    {A B R0 R1 : Subgroup G} (hBA : B ≤ A) (hB : IsElemAbelian p B) (hBc : Nat.card B = p ^ r)
    (hR0 : timmesfeldIsExtraspecial ↥R0) (hx : x ∈ (Subgroup.center ↥R0).map R0.subtype)
    (hAR0 : A ≤ Subgroup.normalizer (R0 : Set G)) (hR1 : IsPGroup 2 R1)
    (hAR1 : A ≤ Subgroup.normalizer (R1 : Set G)) (h01 : R0 < R1) :
    timmesfeldIsExtraspecial ↥R1 := by
  have hp : p.Prime := Fact.out
  have hBC : B ≤ C := fun b hb => (hC b).2 (Subgroup.mem_centralizer_iff.1
    (normalizer_le_centralizer_center hR0 rfl (hAR0 (hBA hb))) x hx).symm
  have hRC : ∀ g ∈ N.map C.subtype, g * x = x * g := fun g hg =>
    (hC g).1 (Subgroup.map_subtype_le N hg)
  have hxZ : x ∈ (Subgroup.center ↥(N.map C.subtype)).map (N.map C.subtype).subtype :=
    mem_center_map_iff.2 ⟨hcR (Subgroup.mem_centralizer_iff.2 hRC), hRC⟩
  have hzp : ∀ W : Subgroup G, x ∈ W → Nat.card W = 2 → Subgroup.zpowers x = W :=
    fun W hxW hW => Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hxW)
      (hW.trans (hx2.symm.trans (Nat.card_zpowers x).symm)).le
  have hZ0 := (hzp _ hxZ (card_center_map_eq_two hR rfl)).symm.trans
    (hzp _ hx (card_center_map_eq_two hR0 rfl))
  have hBR : B ≤ Subgroup.normalizer (N.map C.subtype : Set G) := fun b hb =>
    Subgroup.le_normalizer_map C.subtype
      ⟨⟨b, hBC hb⟩, Subgroup.le_normalizer_of_normal (Subgroup.mem_top _), rfl⟩
  have hBcC : Nat.card (B.subgroupOf C) = p ^ r :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBC).toEquiv).trans hBc
  obtain ⟨hFB, hFBc⟩ := H1017.H1016M5.isElemAbelian_card_map_quot hp hp2 hN e (hB.subgroupOf C)
  have hfix : ∀ H : Subgroup C,
      Nat.card {v : V // ∀ h ∈ H, act (e (QuotientGroup.mk h)) v = v} =
        Nat.card {v : V // ∀ j ∈ H.map (e.toMonoidHom.comp (QuotientGroup.mk' N)), act j v = v} :=
    fun H => Nat.card_congr (Equiv.subtypeEquivRight fun v =>
      ⟨fun h j hj => by obtain ⟨c, hc, rfl⟩ := hj; exact h c hc, fun h c hc => h _ ⟨c, hc, rfl⟩⟩)
  have hcard : ∀ H : Subgroup G, H ≤ C →
      Nat.card ↥(N.map C.subtype ⊓ Subgroup.centralizer (H : Set G)) =
        Nat.card ↥(N ⊓ Subgroup.centralizer (H.subgroupOf C : Set C)) := fun H hH => by
    rw [← map_inf_centralizer_of_le N hH, Subgroup.card_map_of_injective C.subtype_injective]
  refine extraspecial_of_overgroup hp2 hk hR rfl hB hBR ?_ ?_ ?_ hR0 hZ0 (hBA.trans hAR0) hR1
    (hBA.trans hAR1) h01
  · refine (Subgroup.eq_of_le_of_card_ge (le_inf (Subgroup.map_subtype_le _)
      (Subgroup.le_centralizer_iff.1 (hBR.trans (normalizer_le_centralizer_center hR rfl)))) ?_).ge
    rw [card_center_map_eq_two hR rfl, hcard B hBC]
    have h1 : Nat.card {v : V // ∀ h ∈ B.subgroupOf C, act (e (QuotientGroup.mk h)) v = v} ≤ 1 := by
      rw [hfix]
      exact (Nat.card_le_card_of_injective (fun _ => ()) fun a b _ => Subtype.ext
        ((hfixB _ hFB (hFBc.trans hBcC) a a.2).trans
          (hfixB _ hFB (hFBc.trans hBcC) b b.2).symm)).trans_eq Nat.card_unique
    have h2 := hbound (B.subgroupOf C)
    omega
  · intro H hHB hHc
    have hHC := hHB.trans hBC
    obtain ⟨-, hFHc⟩ :=
      H1017.H1016M5.isElemAbelian_card_map_quot hp hp2 hN e ((hB.mono hHB).subgroupOf C)
    have hHcC : Nat.card (H.subgroupOf C) = Nat.card H :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHC).toEquiv
    rw [hcard H hHC, pow_succ']
    refine (hbound _).trans (Nat.mul_le_mul_left 2 ?_)
    rw [hfix]
    refine hfixH _ _ hFB (hFBc.trans hBcC) (Subgroup.map_mono (Subgroup.comap_mono hHB)) ?_
    rw [hFHc, hHcC, hHc, hFBc, hBcC, hBc]
  · intro T hT2 hBT hTZ
    have hTC : T ≤ C := fun t ht =>
      (hC t).2 (Subgroup.mem_centralizer_iff.1 (hTZ ht) x hxZ).symm
    have hle' := hle (B.subgroupOf C) (T.subgroupOf C) (hB.subgroupOf C) hBcC hT2.comap_subtype (by
      rw [← Subgroup.subgroupOf_normalizer_eq hTC]
      exact Subgroup.comap_mono hBT)
    exact fun t ht => ⟨⟨t, hTC ht⟩, hle' (Subgroup.mem_subgroupOf.2 ht), rfl⟩

end Generic


private theorem extraspecial_pCore_map_xGriess :
    timmesfeldIsExtraspecial ↥((CFSG.pCore 2 (cent xGriess)).map (cent xGriess).subtype) := by
  have h := CFSG.Monster.Existence.IsExtraspecialPGroup.of_mulEquiv
    ((CFSG.pCore 2 (cent xGriess)).equivMapOfInjective _ (cent xGriess).subtype_injective)
    twoB_xGriess.1
  exact ⟨h.1, h.2.1.trans h.2.2.1.symm, h.2.2.1, h.2.2.2⟩

private theorem card_pCore_inf_le_GA (H : Subgroup (cent xGriess)) :
    Nat.card ↥(CFSG.pCore 2 (cent xGriess) ⊓ Subgroup.centralizer (H : Set (cent xGriess))) ≤
      2 * Nat.card {v : Fin 24 → ZMod 2 // ∀ h ∈ H,
        (((cosetEquivJ24.trans (MulEquiv.subgroupCongr J24_eq_GA) (QuotientGroup.mk h) : ↥GA) :
          GL (Fin 24) (ZMod 2)) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ v = v} :=
  (card_pCore_inf_centralizer_le H).trans_eq (congrArg (2 * ·) (Nat.card_congr
    (Equiv.subtypeEquivRight fun v => forall₂_congr fun _ _ => Iff.of_eq (congrArg
      (fun M : GL (Fin 24) (ZMod 2) => (M : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ v = v)
      ((MulEquiv.subgroupCongr_apply J24_eq_GA _).symm.trans (congrArg Subtype.val
        (MulEquiv.trans_apply cosetEquivJ24 (MulEquiv.subgroupCongr J24_eq_GA) _).symm))))))

theorem extraspecial_of_xGriess {p r k : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hk : ∀ j, 0 < j → j < k → ¬ 2 ^ j ≡ 1 [MOD p]) (hrk : GLATwoLocalRank p ↥GA < r)
    (hfixB : ∀ F : Subgroup ↥GA, IsElemAbelian p F → Nat.card F = p ^ r →
      ∀ v : Fin 24 → ZMod 2, (∀ j ∈ F, ((j : GL (Fin 24) (ZMod 2)) :
        Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ v = v) → v = 0)
    (hfixH : ∀ F H : Subgroup ↥GA, IsElemAbelian p F → Nat.card F = p ^ r → H ≤ F →
      Nat.card H * p = Nat.card F → Nat.card {v : Fin 24 → ZMod 2 // ∀ j ∈ H,
        ((j : GL (Fin 24) (ZMod 2)) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ v = v} ≤ 2 ^ k)
    {A B R0 R1 : Subgroup MGriess} (hBA : B ≤ A) (hB : IsElemAbelian p B)
    (hBc : Nat.card B = p ^ r) (hR0 : timmesfeldIsExtraspecial ↥R0)
    (hx : xGriess ∈ (Subgroup.center ↥R0).map R0.subtype)
    (hAR0 : A ≤ Subgroup.normalizer (R0 : Set MGriess)) (hR1 : IsPGroup 2 R1)
    (hAR1 : A ≤ Subgroup.normalizer (R1 : Set MGriess)) (h01 : R0 < R1) :
    timmesfeldIsExtraspecial ↥R1 :=
  haveI : Finite MGriess := MGriess_finite_nonabelian_simple.1
  extraspecial_of_quot hp2 hk
    (fun (j : ↥GA) (v : Fin 24 → ZMod 2) =>
      ((j : GL (Fin 24) (ZMod 2)) : Matrix (Fin 24) (Fin 24) (ZMod 2)) *ᵥ v) 0 hfixB hfixH
    orderOf_xGriess (C := cent xGriess) (fun _ => Subgroup.mem_centralizer_singleton_iff)
    extraspecial_pCore_map_xGriess twoB_xGriess.2.2.1 CFSG.pCore_isPGroup
    (fun _ _ => le_pCore_of_normalizer hp2 hrk)
    (cosetEquivJ24.trans (MulEquiv.subgroupCongr J24_eq_GA)) card_pCore_inf_le_GA
    hBA hB hBc hR0 hx hAR0 hR1 hAR1 h01

end CFSG.LocalAnalysis.GLTheoremA.H301B

end
