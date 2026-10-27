module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB516LeafOddJ
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81X10OrthHyp

public section

namespace CFSG.ComponentClassification.GSThmB.Orth516

open CFSG Subgroup CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.TBLit
open CFSG.ComponentClassification.CatLeaf
open CFSG.ComponentClassification.GSThmB.X10Orth (E8Triple)
open CFSG.ComponentClassification.GSThmB.Pump516 (NoCentralInv)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

structure LeafConf {G : Type*} [Group G] (α : MulAut G) (P : Subgroup G) (x : G)
    (J : Subgroup G) : Prop where
  sq : α * α = 1
  ne : α ≠ 1
  PF : P ≤ autFixed α
  Pc : IsPComponent 2 (P.subgroupOf (autFixed α))
  xP : x ∈ P
  x2 : orderOf x = 2
  JC : J ≤ centralizer ({x} : Set G)
  Jc : IsPComponent 2 (J.subgroupOf (centralizer ({x} : Set G)))
  JP : J ≤ P
  Jfix : ∀ j ∈ J, α j = j
  JZ : NoCentralInv J
  J8 : ∀ u ∈ J, ∀ v ∈ J, ∀ w ∈ J, ¬ E8Triple u v w

section Map

variable {G H : Type*} [Group G] [Group H]

theorem map_autFixed (e : G ≃* H) (α : MulAut G) :
    (autFixed α).map e.toMonoidHom = autFixed (MulAut.congr e α) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    change e (α (e.symm (e x))) = e x
    rw [MulEquiv.symm_apply_apply]
    exact congrArg e hx
  · intro hy
    refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    change α (e.symm y) = e.symm y
    apply e.injective
    rw [MulEquiv.apply_symm_apply]
    exact hy

theorem LeafConf.map {α : MulAut G} {P : Subgroup G} {x : G} {J : Subgroup G}
    (h : LeafConf α P x J) (e : G ≃* H) :
    LeafConf (MulAut.congr e α) (P.map e.toMonoidHom) (e x) (J.map e.toMonoidHom) where
  sq := by rw [← map_mul, h.sq, map_one]
  ne := fun h1 => h.ne ((MulAut.congr e).injective (h1.trans (map_one _).symm))
  PF := by
    rw [← map_autFixed]
    exact map_mono h.PF
  Pc := by
    have := CatFactsSp4.isPComponent_map_subgroupOf 2 e h.PF h.Pc
    rwa [map_autFixed] at this
  xP := mem_map_of_mem _ h.xP
  x2 := by rw [MulEquiv.orderOf_eq]; exact h.x2
  JC := by
    rw [← CatFactsSp4.map_centralizer_singleton]
    exact map_mono h.JC
  Jc := by
    have := CatFactsSp4.isPComponent_map_subgroupOf 2 e h.JC h.Jc
    rwa [CatFactsSp4.map_centralizer_singleton] at this
  JP := map_mono h.JP
  Jfix := by
    rintro _ ⟨j, hj, rfl⟩
    change e (α (e.symm (e j))) = e j
    rw [MulEquiv.symm_apply_apply, h.Jfix j hj]
  JZ := h.JZ.map e
  J8 := by
    rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩ _ ⟨w, hw, rfl⟩ hT
    exact h.J8 u hu v hv w hw (X10Orth.E8Triple.comap (φ := e.toMonoidHom) e.injective hT)

end Map

variable {S : Type} [Group S] [Finite S]

theorem noE8_of_lieModel {J : Subgroup S} {p f : ℕ} (hp2 : p ≠ 2)
    (hJm : Blueprint.LieModel (J ⧸ pPrimeCore 2 J) .PSL 2 p (2 * f)) :
    ∀ u ∈ J, ∀ v ∈ J, ∀ w ∈ J, ¬ E8Triple u v w := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hp, -, F, _, _, hF, ⟨e⟩⟩ := CFSG.GH74.Generic.lieModel_psl_data hJm
  intro u hu v hv w hw hT
  have hT3 : E8Triple (⟨u, hu⟩ : J) ⟨v, hv⟩ ⟨w, hw⟩ :=
    X10Orth.E8Triple.comap (φ := J.subtype) J.subtype_injective hT
  have hodd : Odd (Nat.card F) := by
    rw [hF]
    exact (hp.odd_of_ne_two hp2).pow
  have h2 : (2 : F) ≠ 0 := CatalogueBOddQuadratic.two_ne_zero_of_odd_card hodd
  refine X10Orth.false_of_statedProjSL h2 (hT3.map (e.toMonoidHom.comp
    (QuotientGroup.mk' (pPrimeCore 2 ↥J))) fun g hg h1 => ?_)
  have h1' : QuotientGroup.mk' (pPrimeCore 2 ↥J) g = 1 :=
    e.injective (by rw [map_one]; exact h1)
  have hgO : g ∈ pPrimeCore 2 ↥J := (QuotientGroup.eq_one_iff g).mp h1'
  have hd2 : orderOf g ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact hg)
  have hdO : orderOf g ∣ Nat.card (pPrimeCore 2 ↥J) := by
    have := orderOf_dvd_natCard (⟨g, hgO⟩ : pPrimeCore 2 ↥J)
    rwa [Subgroup.orderOf_mk] at this
  have hcop := pPrimeCore_coprime_card (p := 2) (G := ↥J)
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop hd2 hdO)

omit [Finite S] in
theorem commutator_top_of_perfect {J : Subgroup S} (hJp : ⁅J, J⁆ = J) : commutator J = ⊤ := by
  apply Subgroup.map_injective J.subtype_injective
  rw [Subgroup.map_subtype_commutator, hJp, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

omit [Finite S] in
theorem le_of_le_sup_oddCoreIn {J JB : Subgroup S} (hJp : ⁅J, J⁆ = J) (hJBJ : JB ≤ J)
    (hZ : pPrimeCore 2 J ≤ center J) (hJ : J ≤ JB ⊔ oddCoreIn J) : J ≤ JB := by
  have hOJ : oddCoreIn J ≤ J := map_subtype_le _
  have hsup : JB.subgroupOf J ⊔ pPrimeCore 2 J = ⊤ := by
    have e1 : (oddCoreIn J).subgroupOf J = pPrimeCore 2 J :=
      Subgroup.comap_map_eq_self_of_injective J.subtype_injective _
    rw [← e1, ← subgroupOf_sup hJBJ hOJ]
    exact (subgroupOf_eq_top).2 hJ
  have htop : (⊤ : Subgroup J) ≤ JB.subgroupOf J := by
    calc (⊤ : Subgroup J) = commutator J := (commutator_top_of_perfect hJp).symm
      _ = ⁅JB.subgroupOf J ⊔ pPrimeCore 2 J, JB.subgroupOf J ⊔ pPrimeCore 2 J⁆ := by
          rw [hsup, commutator_def]
      _ = ⁅JB.subgroupOf J, JB.subgroupOf J⁆ :=
          CatalogueBPrimeJoin.commutator_sup_central _ _ hZ
      _ ≤ JB.subgroupOf J := commutator_le_self _
  intro j hj
  exact mem_subgroupOf.1 (htop (mem_top ⟨j, hj⟩))

omit [Finite S] in
theorem fix_of_mem_oddCoreIn {J : Subgroup S} (hJp : ⁅J, J⁆ = J)
    (hZ : pPrimeCore 2 J ≤ center J) {σ : MulAut S} (hσJ : ∀ j ∈ J, σ j ∈ J)
    (hσO : ∀ j ∈ J, j⁻¹ * σ j ∈ oddCoreIn J) : ∀ j ∈ J, σ j = j := by
  have hcen : ∀ j : J, ∀ y : J, (j : S)⁻¹ * σ j * y = y * ((j : S)⁻¹ * σ j) := by
    intro j y
    obtain ⟨z, hz, hzj⟩ := hσO j j.2
    have hzc := mem_center_iff.1 (hZ hz) y
    rw [← hzj]
    exact congrArg Subtype.val hzc.symm
  let δ : J →* J :=
    { toFun := fun j => ⟨(j : S)⁻¹ * σ j, mul_mem (inv_mem j.2) (hσJ j j.2)⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun j k => Subtype.ext (by
        change ((j : S) * k)⁻¹ * σ ((j : S) * k) = ((j : S)⁻¹ * σ j) * ((k : S)⁻¹ * σ k)
        have h := hcen j k⁻¹
        simp only [coe_inv] at h
        rw [map_mul, mul_inv_rev]
        calc (k : S)⁻¹ * (j : S)⁻¹ * (σ j * σ k) = (k : S)⁻¹ * ((j : S)⁻¹ * σ j) * σ k := by
              group
          _ = ((j : S)⁻¹ * σ j) * (k : S)⁻¹ * σ k := by rw [h]
          _ = _ := by group) }
  have hker : commutator J ≤ δ.ker := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, map_commutatorElement]
    apply commutatorElement_eq_one_iff_mul_comm.2
    exact Subtype.ext (hcen a (δ b))
  intro j hj
  have h1 : δ ⟨j, hj⟩ = 1 := hker (by rw [commutator_top_of_perfect hJp]; exact mem_top _)
  have h2 := congrArg Subtype.val h1
  change j⁻¹ * σ j = 1 at h2
  calc σ j = j * (j⁻¹ * σ j) := by group
    _ = j := by rw [h2, mul_one]

theorem leafConf_of_leaf [IsSimpleGroup S] (hQ : FixedTwoComponentsQuasisimple S)
    (hna : ∃ x y : S, x * y ≠ y * x) {σ : MulAut S} {P : Subgroup S}
    (hP : ProperFixedComponent σ P) {t : S} (ht : t ∈ P) (ht2 : orderOf t = 2)
    {J : Subgroup S} (hJC : J ≤ centralizer ({t} : Set S))
    (hJ : IsPComponent 2 (J.subgroupOf (centralizer ({t} : Set S)))) {p f : ℕ} (hp2 : p ≠ 2)
    (hJm : Blueprint.LieModel (J ⧸ pPrimeCore 2 J) .PSL 2 p (2 * f))
    (hσJ : ∀ j ∈ J, σ j ∈ J) (hσO : ∀ j ∈ J, j⁻¹ * σ j ∈ oddCoreIn J) {JB : Subgroup S}
    (hJB : JB ≤ J ⊓ P) (hJBs : J ≤ JB ⊔ oddCoreIn J) : LeafConf σ P t J := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hσ1 : σ ≠ 1 := hP.ne_one
  obtain ⟨hσ2', hPF, hPp, -⟩ := hP
  obtain ⟨-, hJc, hJZ, -⟩ := Pump516.leaf_J_data hQ hna ht2 hJC hJ hJm
  have hJα : J ≤ fixedSubgroup (MulAut.conj t) := by
    rw [Pump516.fixedSubgroup_conj]
    exact hJC
  have hq : IsQuasisimple J :=
    LocalCores.isQuasisimple_of_mulEquiv (subgroupOfEquivOfLe hJα) hJc.1
  have hJp : ⁅J, J⁆ = J := by
    have : Group.IsPerfect J := hq.1
    exact Subgroup.isPerfect_iff.1 this
  have hs : IsSimpleGroup (J ⧸ pPrimeCore 2 J) :=
    Pump516.isSimpleGroup_of_lieModel_psl (by norm_num) hJm
  have hZ : pPrimeCore 2 J ≤ center J := by
    rcases LieType.CurtisTits.le_center_or_eq_top_of_isQuasisimple hq (pPrimeCore 2 J) with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hs.toNontrivial.exists_pair_ne
      obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
      obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
      apply hab
      rw [QuotientGroup.eq_iff_div_mem, h]
      exact mem_top _
  refine ⟨?_, hσ1, hPF, hPp, ht, ht2, hJC, hJ,
    (le_of_le_sup_oddCoreIn hJp (hJB.trans inf_le_left) hZ hJBs).trans (hJB.trans inf_le_right),
    fix_of_mem_oddCoreIn hJp hZ hσJ hσO, ?_, noE8_of_lieModel hp2 hJm⟩
  · exact MulEquiv.ext fun y => hσ2' y
  · intro z hz hzc hzz
    have h1 := hJZ ⟨z, hJα hz⟩ (mem_subgroupOf.2 hz)
      (fun y hy => Subtype.ext (hzc y (mem_subgroupOf.1 hy))) (Subtype.ext hzz)
    exact congrArg Subtype.val h1

end CFSG.ComponentClassification.GSThmB.Orth516
