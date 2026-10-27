module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.GN.C126GenLift4

public section

namespace CFSG.AGLEmbeddingD2.GN

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.B6 Equiv
  CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G] {N : ℕ}

omit [Finite G] in
theorem coe_mem_pCoreOf_iff' (H : Subgroup G) (x : ↥H) :
    (x : G) ∈ pCoreOf 2 H ↔ x ∈ CFSG.pCore 2 ↥H := by
  constructor
  · rintro ⟨y, hy, hyx⟩
    have : y = x := Subtype.ext hyx
    rwa [← this]
  · intro hx
    exact ⟨x, hx, rfl⟩

namespace SymLift

variable {H T M V Y : Subgroup G} {hV : IsElemAbelian 2 V} {s : GenSetting H T M V Y hV}
  {d : GenData N H T V Y hV}

namespace XData

variable {x : G} (hx : XData s d x)

include hx

omit [Finite G] in
theorem cv_mem_L {k : G} (hk : k ∈ Khat s d x) : cv hV k ∈ d.L :=
  (mem_A₁.1 (hx.Khat_le_A₁ hk)).2

@[expose] noncomputable def phi : ↥(Khat s d x) →* Perm (Fin N) where
  toFun k := d.th (cv hV (k : G))
  map_one' := by
    show d.th (cv hV (1 : G)) = 1
    rw [cv_one, d.th_one]
  map_mul' k k' := by
    show d.th (cv hV ((k : G) * (k' : G))) = d.th (cv hV (k : G)) * d.th (cv hV (k' : G))
    have hkN := s.H_le_N (hx.Khat_le_H k.2)
    have hk'N := s.H_le_N (hx.Khat_le_H k'.2)
    rw [cv_mul hV hkN hk'N, d.th_mul (hx.cv_mem_L k.2) (hx.cv_mem_L k'.2)]

omit [Finite G] in
theorem phi_mem_alt (k : ↥(Khat s d x)) : hx.phi k ∈ alternatingGroup (Fin N) := by
  let Alt1 : Subgroup G :=
    { carrier := {g | g ∈ A₁ s d ∧ d.th (cv hV g) ∈ alternatingGroup (Fin N)}
      one_mem' := ⟨(A₁ s d).one_mem, by
        rw [cv_one, d.th_one]
        exact Subgroup.one_mem _⟩
      mul_mem' := fun {a b} ha hb => ⟨(A₁ s d).mul_mem ha.1 hb.1, by
        have haH := (mem_A₁.1 ha.1).1
        have hbH := (mem_A₁.1 hb.1).1
        rw [cv_mul hV (s.H_le_N haH) (s.H_le_N hbH),
          d.th_mul (mem_A₁.1 ha.1).2 (mem_A₁.1 hb.1).2]
        exact Subgroup.mul_mem _ ha.2 hb.2⟩
      inv_mem' := fun {a} ha => ⟨(A₁ s d).inv_mem ha.1, by
        have haH := (mem_A₁.1 ha.1).1
        rw [cv_inv hV (s.H_le_N haH), d.th_inv (mem_A₁.1 ha.1).2]
        exact Subgroup.inv_mem _ ha.2⟩ }
  have hxA : x ∈ Alt1 := ⟨hx.x_mem_A₁, by
    rw [hx.th_eq]; exact (isThreeCycle_c3 d.hab d.hbp d.hap).mem_alternatingGroup⟩
  have hz : Subgroup.zpowers x ≤ Alt1 := by rw [Subgroup.zpowers_le]; exact hxA
  have hK : Khat s d x ≤ Alt1 := by
    show conjClosure (Subgroup.zpowers x) (A₁ s d) ≤ Alt1
    refine conjClosure_le fun a ha z hz' => ?_
    have haH := (mem_A₁.1 ha).1
    have hzA := hx.zpowers_le_A₁ hz'
    refine ⟨(A₁ s d).mul_mem ((A₁ s d).mul_mem ha hzA) ((A₁ s d).inv_mem ha), ?_⟩
    have hzH := (mem_A₁.1 hzA).1
    rw [cv_mul hV (Subgroup.mul_mem _ (s.H_le_N haH) (s.H_le_N hzH)) (s.H_le_N (H.inv_mem haH)),
      cv_mul hV (s.H_le_N haH) (s.H_le_N hzH), cv_inv hV (s.H_le_N haH),
      d.th_mul (d.L.mul_mem (mem_A₁.1 ha).2 (mem_A₁.1 hzA).2) (d.L.inv_mem (mem_A₁.1 ha).2),
      d.th_mul (mem_A₁.1 ha).2 (mem_A₁.1 hzA).2, d.th_inv (mem_A₁.1 ha).2]
    have hzalt : d.th (cv hV z) ∈ alternatingGroup (Fin N) := (hz hz').2
    exact Subgroup.Normal.conj_mem (inferInstance : (alternatingGroup (Fin N)).Normal) _ hzalt _
  exact (hK k.2).2

@[expose] noncomputable def alpha : ↥(Khat s d x) →* ↥(alternatingGroup (Fin N)) :=
  hx.phi.codRestrict (alternatingGroup (Fin N)) hx.phi_mem_alt

omit [Finite G] in
theorem alpha_apply (k : ↥(Khat s d x)) : ((hx.alpha k : ↥(alternatingGroup (Fin N))) :
    Perm (Fin N)) = d.th (cv hV (k : G)) := rfl

omit [Finite G] in
theorem alpha_surj : Function.Surjective hx.alpha := by
  intro g
  have hg : (g : Perm (Fin N)) ∈ alternatingGroup (Fin N) := g.2
  obtain ⟨h, hhF, hθ⟩ := hx.coversAlt (g : Perm (Fin N)) hg
  have hKN : Khat s d x ≤ Subgroup.normalizer (V : Set G) := hx.Khat_le_H.trans s.H_le_N
  obtain ⟨k, hk, hkh⟩ := (mem_autI_iff hV hKN).1 hhF
  refine ⟨⟨k, hk⟩, Subtype.ext ?_⟩
  rw [alpha_apply, hkh, d.th_of_mem h.2]
  exact hθ

omit [Finite G] in
theorem alpha_eq_one_iff (k : ↥(Khat s d x)) : hx.alpha k = 1 ↔ cv hV (k : G) = 1 := by
  rw [Subtype.ext_iff, alpha_apply]
  show d.th (cv hV (k : G)) = (1 : Perm (Fin N)) ↔ _
  constructor
  · intro h
    exact d.th_inj (hx.cv_mem_L k.2) d.L.one_mem (by rw [h, d.th_one])
  · intro h
    rw [h, d.th_one]

omit [Finite G] in
theorem alpha_ker_C :
    hx.alpha.ker = (Subgroup.centralizer (V : Set G)).subgroupOf (Khat s d x) := by
  ext k
  rw [MonoidHom.mem_ker, alpha_eq_one_iff, Subgroup.mem_subgroupOf]
  exact cv_eq_one_iff hV (s.H_le_N (hx.Khat_le_H k.2))

theorem alpha_ker (hRad : twoResidual H ⊓ Subgroup.centralizer (V : Set G) ≤ pCoreOf 2 H) :
    hx.alpha.ker = CFSG.pCore 2 ↥(Khat s d x) := by
  ext k
  rw [← coe_mem_pCoreOf_iff', hx.pCoreOf_Khat, hx.alpha_ker_C, Subgroup.mem_subgroupOf]
  constructor
  · intro hc
    exact ⟨k.2, hx.Khat_inf_C hRad ⟨k.2, hc⟩⟩
  · intro hq
    exact s.Q_le_C hq.2

end XData

end SymLift

namespace SymLift

variable {H T M V Y : Subgroup G} {hV : IsElemAbelian 2 V} {s : GenSetting H T M V Y hV}
  {d : GenData N H T V Y hV}

namespace XData

variable {x : G} (hx : XData s d x) (hY : IsShort2 Y) (hA3 : IsAltType Y 3)

include hx hY hA3

@[expose] noncomputable def betaEquiv :
    ↥(blockU (Khat s d x)) ≃* Multiplicative (evenWeight N) :=
  (MulEquiv.subgroupCongr (hx.blockU_eq_Vc hY hA3)).trans
    ((Subgroup.equivMapOfInjective (commV d.L) (valHom hV) IntMod.val_injective).symm.trans d.β)

theorem betaEquiv_apply (u : ↥(blockU (Khat s d x))) (w : ↥(commV d.L))
    (hw : (w : IntMod V hV).val = (u : G)) : hx.betaEquiv hY hA3 u = d.β w := by
  have h : (Subgroup.equivMapOfInjective (commV d.L) (valHom hV) IntMod.val_injective) w =
      MulEquiv.subgroupCongr (hx.blockU_eq_Vc hY hA3) u :=
    Subtype.ext (by show (w : IntMod V hV).val = (u : G); exact hw)
  show d.β ((Subgroup.equivMapOfInjective (commV d.L) (valHom hV) IntMod.val_injective).symm
    (MulEquiv.subgroupCongr (hx.blockU_eq_Vc hY hA3) u)) = d.β w
  rw [← h]
  simp

theorem exists_betaPre (u : ↥(blockU (Khat s d x))) :
    ∃ w : ↥(commV d.L), (w : IntMod V hV).val = (u : G) := by
  have hu : (u : G) ∈ Vc d := hx.blockU_eq_Vc hY hA3 ▸ u.2
  obtain ⟨w, hw, hwu⟩ := mem_Vc.1 hu
  exact ⟨⟨w, hw⟩, hwu⟩

theorem isAltType_N (hRad : twoResidual H ⊓ Subgroup.centralizer (V : Set G) ≤ pCoreOf 2 H) :
    IsAltType (Khat s d x) N := by
  refine ⟨hx.alpha, hx.alpha_surj, hx.alpha_ker hRad, (hx.betaEquiv hY hA3).toMonoidHom,
    (hx.betaEquiv hY hA3).surjective, ?_, ?_⟩
  · rw [hx.blockZ_eq_bot hY hA3, Subgroup.bot_subgroupOf]
    exact (MonoidHom.ker_eq_bot_iff _).2 (hx.betaEquiv hY hA3).injective
  · intro ℓ u v huv i
    obtain ⟨u', hu'⟩ := hx.exists_betaPre hY hA3 u
    have hℓ : cv hV (ℓ : G) ∈ d.L := hx.cv_mem_L ℓ.2
    set ℓ' : ↥d.L := ⟨cv hV (ℓ : G), hℓ⟩ with hℓ'
    have hu'' : ((ℓ' : MulAut (IntMod V hV)) (u' : IntMod V hV)) ∈ commV d.L :=
      act_mem_commV' hℓ u'.2
    have hℓN : (ℓ : G) ∈ Subgroup.normalizer (V : Set G) := s.H_le_N (hx.Khat_le_H ℓ.2)
    have hv' : ((⟨(ℓ' : MulAut (IntMod V hV)) (u' : IntMod V hV), hu''⟩ : ↥(commV d.L)) :
        IntMod V hV).val = (v : G) := by
      show ((cv hV (ℓ : G)) (u' : IntMod V hV)).val = _
      rw [cv_val hV hℓN, hu', huv]
      rfl
    have h1 := hx.betaEquiv_apply hY hA3 v _ hv'
    have h2 := hx.betaEquiv_apply hY hA3 u u' hu'
    have h3 := d.hβ ℓ' u' hu'' i
    have h4 : ((hx.alpha ℓ : ↥(alternatingGroup (Fin N))) : Perm (Fin N)) = d.θ ℓ' := by
      rw [alpha_apply, d.th_of_mem hℓ]
    show ((Multiplicative.toAdd ((hx.betaEquiv hY hA3) v) : evenWeight N) : Fin N → ZMod 2) i = _
    rw [h1, h4]
    show _ = ((Multiplicative.toAdd ((hx.betaEquiv hY hA3) u) : evenWeight N) :
      Fin N → ZMod 2) _
    rw [h2]
    exact h3

end XData

end SymLift

end CFSG.AGLEmbeddingD2.GN
