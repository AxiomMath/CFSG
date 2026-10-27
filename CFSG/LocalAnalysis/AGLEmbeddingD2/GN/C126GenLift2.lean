module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.GN.C126GenData
public import CFSG.Quasithin.Background.A4Reduced
public import CFSG.Quasithin.Background.C1PackSubnormal

public section

namespace CFSG.AGLEmbeddingD2.GN

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.B6 Equiv
  CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G] {N : ℕ}

theorem mem_O2_of_odd {H : Subgroup G} {x : G} (hx : x ∈ H) (ho : Odd (orderOf x)) :
    x ∈ twoResidual H := by
  obtain ⟨b, hb⟩ := twoResidual_isTwoQuotient H x hx
  exact B6.mem_of_pow_mem_of_coprime hb (Nat.Coprime.pow_right b (Odd.coprime_two_right ho))

namespace SymLift

variable {H T M V Y : Subgroup G} {hV : IsElemAbelian 2 V} {s : GenSetting H T M V Y hV}
  {d : GenData N H T V Y hV}

structure XData (s : GenSetting H T M V Y hV) (d : GenData N H T V Y hV) (x : G) : Prop where
  mem : x ∈ Y
  ord : orderOf x = 3
  mem_L : cv hV x ∈ d.L
  th_eq : d.th (cv hV x) = c3 d.a d.b d.p

@[expose] def Khat (s : GenSetting H T M V Y hV) (d : GenData N H T V Y hV) (x : G) : Subgroup G :=
  conjClosure (Subgroup.zpowers x) (A₁ s d)

omit [Finite G] in
theorem zpowers_le_Khat (s : GenSetting H T M V Y hV) (d : GenData N H T V Y hV) (x : G) :
    Subgroup.zpowers x ≤ Khat s d x := le_conjClosure _ _

omit [Finite G] in
theorem A₁_le_normalizer_Khat (s : GenSetting H T M V Y hV) (d : GenData N H T V Y hV) (x : G) :
    A₁ s d ≤ Subgroup.normalizer (Khat s d x : Set G) := le_normalizer_conjClosure _ _

namespace XData

variable {x : G} (hx : XData s d x)

include hx

omit [Finite G] in
theorem x_mem_A₁ : x ∈ A₁ s d := Y_le_A₁ (s := s) (d := d) hx.mem

omit [Finite G] in
theorem zpowers_le_A₁ : Subgroup.zpowers x ≤ A₁ s d := by
  rw [Subgroup.zpowers_le]; exact hx.x_mem_A₁

omit [Finite G] in
theorem Khat_le_A₁ : Khat s d x ≤ A₁ s d :=
  conjClosure_le fun _ ha _ hz => (A₁ s d).mul_mem ((A₁ s d).mul_mem ha (hx.zpowers_le_A₁ hz))
    ((A₁ s d).inv_mem ha)

omit [Finite G] in
theorem Khat_le_H : Khat s d x ≤ H := hx.Khat_le_A₁.trans A₁_le_H

theorem Y_le_Khat : Y ≤ Khat s d x := by
  set Y₀ := conjClosure (Subgroup.zpowers x) Y with hY₀
  have hxY : Subgroup.zpowers x ≤ Y := by rw [Subgroup.zpowers_le]; exact hx.mem
  have hY₀Y : Y₀ ≤ Y := conjClosure_le fun y hy z hz => Y.mul_mem (Y.mul_mem hy (hxY hz))
    (Y.inv_mem hy)
  have hnY : Y ≤ Subgroup.normalizer (Y₀ : Set G) := le_normalizer_conjClosure _ _
  have hsup : (Y ⊓ pCoreOf 2 H) ⊔ Y₀ = Y := by
    apply le_antisymm (sup_le inf_le_left hY₀Y)
    calc Y = (Y ⊓ pCoreOf 2 H) ⊔ Subgroup.zpowers x := s.Y_eq_sup hx.mem hx.ord
      _ ≤ (Y ⊓ pCoreOf 2 H) ⊔ Y₀ := sup_le_sup_left (le_conjClosure _ _) _
  have h2 := isTwoQuotient_of_sup_eq ((pCoreOf_isPGroup 2 H).to_le inf_le_right) hnY hsup
  have : twoResidual Y ≤ Y₀ := twoResidual_le_of_isTwoQuotient hY₀Y hnY h2
  rw [s.Y_res] at this
  exact this.trans (conjClosure_mono le_rfl (Y_le_A₁ (s := s) (d := d)))

theorem Khat_le_twoResidual : Khat s d x ≤ twoResidual H := by
  have hxK : x ∈ twoResidual H :=
    mem_O2_of_odd (s.Y_le hx.mem) (by rw [hx.ord]; decide)
  refine conjClosure_le fun a ha z hz => ?_
  have hzK : z ∈ twoResidual H := by
    have : Subgroup.zpowers x ≤ twoResidual H := by rw [Subgroup.zpowers_le]; exact hxK
    exact this hz
  exact (Subgroup.mem_normalizer_iff.1 (le_normalizer_twoResidual H (A₁_le_H ha)) z).1 hzK

theorem Khat_inf_C (hRad : twoResidual H ⊓ Subgroup.centralizer (V : Set G) ≤ pCoreOf 2 H) :
    Khat s d x ⊓ Subgroup.centralizer (V : Set G) ≤ pCoreOf 2 H :=
  fun _ hk => hRad ⟨hx.Khat_le_twoResidual hk.1, hk.2⟩

end XData

end SymLift

namespace SymLift

variable {H T M V Y : Subgroup G} {hV : IsElemAbelian 2 V} {s : GenSetting H T M V Y hV}
  {d : GenData N H T V Y hV}

variable (s) in
@[expose] def Jt : Subgroup G where
  carrier := {g | g ∈ H ∧ cv hV g ∈ autI hV (thompsonJ H)}
  one_mem' := ⟨H.one_mem, by
    rw [cv_of_mem hV (Subgroup.one_mem _)]
    exact (show convI hV (1 : Subgroup.normalizer (V : Set G)) = 1 from map_one _) ▸
      (autI hV (thompsonJ H)).one_mem⟩
  mul_mem' := fun {a b} ha hb => ⟨H.mul_mem ha.1 hb.1, by
    rw [cv_mul hV (s.H_le_N ha.1) (s.H_le_N hb.1)]; exact (autI hV (thompsonJ H)).mul_mem ha.2 hb.2⟩
  inv_mem' := fun {a} ha => ⟨H.inv_mem ha.1, by
    rw [cv_inv hV (s.H_le_N ha.1)]; exact (autI hV (thompsonJ H)).inv_mem ha.2⟩

omit [Finite G] in
theorem A₁_le_Jt : A₁ s d ≤ Jt s := fun _ ha => ⟨(mem_A₁.1 ha).1, d.L_J (mem_A₁.1 ha).2⟩

omit [Finite G] in
theorem Jt_le_H : Jt s ≤ H := fun _ hg => hg.1

omit [Finite G] in
theorem conj_mem_A₁ {j a : G} (hj : j ∈ Jt s) (ha : a ∈ A₁ s d) : j * a * j⁻¹ ∈ A₁ s d := by
  obtain ⟨haH, haL⟩ := mem_A₁.1 ha
  have hjN : cv hV j ∈ Subgroup.normalizer (d.L : Set (MulAut (IntMod V hV))) := d.J_N hj.2
  refine mem_A₁.2 ⟨H.mul_mem (H.mul_mem hj.1 haH) (H.inv_mem hj.1), ?_⟩
  rw [cv_mul hV (Subgroup.mul_mem _ (s.H_le_N hj.1) (s.H_le_N haH)) (s.H_le_N (H.inv_mem hj.1)),
    cv_mul hV (s.H_le_N hj.1) (s.H_le_N haH), cv_inv hV (s.H_le_N hj.1)]
  exact (Subgroup.mem_normalizer_iff.1 hjN (cv hV a)).1 haL

omit [Finite G] in
theorem Jt_normalizes_A₁ : Jt s ≤ Subgroup.normalizer (A₁ s d : Set G) := by
  intro j hj
  rw [Subgroup.mem_normalizer_iff]
  intro a
  refine ⟨fun ha => conj_mem_A₁ hj ha, fun h => ?_⟩
  have := conj_mem_A₁ (Subgroup.inv_mem _ hj) h
  simpa [mul_assoc] using this

omit [Finite G] in
theorem H_normalizes_Jt : H ≤ Subgroup.normalizer (Jt s : Set G) := by
  intro h hh
  rw [Subgroup.mem_normalizer_iff]
  have key : ∀ h ∈ H, ∀ j ∈ Jt s, h * j * h⁻¹ ∈ Jt s := by
    intro h hh j hj
    refine ⟨H.mul_mem (H.mul_mem hh hj.1) (H.inv_mem hh), ?_⟩
    obtain ⟨j₀, hj₀, hcv⟩ := (mem_autI_iff hV ((thompsonJ_le H).trans s.H_le_N)).1 hj.2
    have hj₀H : j₀ ∈ H := thompsonJ_le H hj₀
    have e : cv hV (h * j * h⁻¹) = cv hV (h * j₀ * h⁻¹) := by
      rw [cv_mul hV (Subgroup.mul_mem _ (s.H_le_N hh) (s.H_le_N hj.1)) (s.H_le_N (H.inv_mem hh)),
        cv_mul hV (s.H_le_N hh) (s.H_le_N hj.1),
        cv_mul hV (Subgroup.mul_mem _ (s.H_le_N hh) (s.H_le_N hj₀H)) (s.H_le_N (H.inv_mem hh)),
        cv_mul hV (s.H_le_N hh) (s.H_le_N hj₀H), hcv]
    rw [e]
    have hmem : h * j₀ * h⁻¹ ∈ thompsonJ H :=
      (Subgroup.mem_normalizer_iff.1 (le_normalizer_thompsonJ H hh) j₀).1 hj₀
    exact (mem_autI_iff hV ((thompsonJ_le H).trans s.H_le_N)).2 ⟨_, hmem, rfl⟩
  intro j
  exact ⟨fun hj => key h hh j hj, fun hj => by
    simpa [mul_assoc] using key h⁻¹ (H.inv_mem hh) _ hj⟩

namespace XData

variable {x : G} (hx : XData s d x)

include hx

omit [Finite G] in
theorem Khat_normal_in_A₁ : ((Khat s d x).subgroupOf (A₁ s d)).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer hx.Khat_le_A₁).2
    (A₁_le_normalizer_Khat s d x)

omit [Finite G] in
theorem Khat_isSubnormal : IsSubnormal (Khat s d x) H := by
  refine IsSubnormal.step hx.Khat_le_A₁ hx.Khat_normal_in_A₁ ?_
  refine IsSubnormal.step A₁_le_Jt ((Subgroup.normal_subgroupOf_iff_le_normalizer A₁_le_Jt).2
    Jt_normalizes_A₁) ?_
  exact IsSubnormal.step Jt_le_H ((Subgroup.normal_subgroupOf_iff_le_normalizer Jt_le_H).2
    H_normalizes_Jt) (IsSubnormal.refl H)

omit [Finite G] in
theorem Khat_subgroupOf_isSubnormal : ((Khat s d x).subgroupOf H).IsSubnormal := by
  have h1 : ((Khat s d x).subgroupOf (A₁ s d)).IsSubnormal := hx.Khat_normal_in_A₁.isSubnormal
  have h2 : ((A₁ s d).subgroupOf (Jt s)).IsSubnormal :=
    ((Subgroup.normal_subgroupOf_iff_le_normalizer A₁_le_Jt).2 Jt_normalizes_A₁).isSubnormal
  have h3 : ((Jt s).subgroupOf H).IsSubnormal :=
    ((Subgroup.normal_subgroupOf_iff_le_normalizer Jt_le_H).2 H_normalizes_Jt).isSubnormal
  exact C1Pack.isSubnormal_subgroupOf_trans' (hx.Khat_le_A₁.trans A₁_le_Jt) Jt_le_H
    (C1Pack.isSubnormal_subgroupOf_trans' hx.Khat_le_A₁ A₁_le_Jt h1 h2) h3

theorem charTwo_Khat : CharTwo (Khat s d x) :=
  A4.charTwo_of_subnormal hx.Khat_isSubnormal s.charTwo

theorem pCoreOf_Khat : pCoreOf 2 (Khat s d x) = Khat s d x ⊓ pCoreOf 2 H := by
  apply le_antisymm
  · exact le_inf (pCoreOf_le 2 _) (A4.pCoreOf_le_of_subnormal 2 hx.Khat_isSubnormal)
  · refine le_pCoreOf_of_le_normalizer 2 inf_le_left ?_ ((pCoreOf_isPGroup 2 H).to_le inf_le_right)
    intro k hk
    exact Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer hk, le_normalizer_pCoreOf 2 H (hx.Khat_le_H hk)⟩

end XData

end SymLift

end CFSG.AGLEmbeddingD2.GN
