module

public import CFSG.ClassicalInvolution.Q3.Q3TLSub
public import CFSG.ClassicalInvolution.Q3.Q3TLPat
public import CFSG.ClassicalInvolution.Q3.Q3TLOuter
public import CFSG.ClassicalInvolution.Q3.Q3TJD4Out

public section

namespace CFSG.ClassicalInvolution.Q3.Q3T

open Module QuadraticMap CFSG.LieType.Universal.Spin CFSG.Assembly.LowTwoRank
open CFSG.Open (IsSubnormal classicalInvolutionOddCore)
open CFSG.ClassicalGroups.Orthogonal CFSG.ClassicalGroups.Orthogonal.Small
open CFSG.ClassicalInvolution.ModelFacts CFSG.ClassicalInvolution.Balance
open CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusBorel
open CFSG.LocalAnalysis.ComponentInitial
open scoped MatrixGroups

theorem isSubnormal_map_hom {G G' : Type*} [Group G] [Group G'] (f : G →* G')
    {H K : Subgroup G} (h : IsSubnormal H K) : IsSubnormal (H.map f) (K.map f) :=
  h.map f

variable {Y : Type} [Group Y] [Finite Y] {L : Subgroup Y} {z : Y}

omit [Finite Y] in
theorem map_centralizer_eq {T : Subgroup Y} {P : Type*} [Group P] (e : T ≃* P) (hzT : z ∈ T) :
    (Subgroup.centralizer ({e ⟨z, hzT⟩} : Set P)).map (T.subtype.comp e.symm.toMonoidHom) =
      T ⊓ Subgroup.centralizer ({z} : Set Y) := by
  ext y
  constructor
  · rintro ⟨p, hp, rfl⟩
    refine ⟨(e.symm p).2, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    have h1 := congrArg (fun q => (e.symm q : Y)) (Subgroup.mem_centralizer_singleton_iff.mp hp)
    simpa using h1
  · rintro ⟨hyT, hyz⟩
    refine ⟨e ⟨y, hyT⟩, Subgroup.mem_centralizer_singleton_iff.mpr ?_, by simp⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp hyz)

omit [Finite Y] in
theorem congr_conjNormal_apply_eq {T : Subgroup Y} [T.Normal] {P : Type*} [Group P] (e : T ≃* P)
    {x : Y} {p : P} (h : x * (e.symm p : Y) = (e.symm p : Y) * x) :
    MulAut.congr e (MulAut.conjNormal x : MulAut T) p = p := by
  have h1 : MulAut.conjNormal x (e.symm p) = e.symm p := Subtype.ext (by
    rw [MulAut.conjNormal_apply, h, mul_inv_cancel_right])
  rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply, h1,
    MulEquiv.apply_symm_apply]

omit [Finite Y] in
theorem inf_centralizer_normal (T : Subgroup Y) [hTn : T.Normal] (z : Y) :
    ((T ⊓ Subgroup.centralizer ({z} : Set Y)).subgroupOf
      (Subgroup.centralizer ({z} : Set Y))).Normal := by
  rw [Subgroup.normal_subgroupOf_iff inf_le_right]
  intro a c ha hc
  exact ⟨hTn.conj_mem _ ha.1 _, Subgroup.mul_mem _ (Subgroup.mul_mem _ hc ha.2)
    (Subgroup.inv_mem _ hc)⟩

section Comm

variable {K : Type} [Field K] (g : StatedOmega (StatedQuadPlus 4 K))
  (hc : IsCompl (plusSp (toLinEquiv _ K g.val)) (minusSp (toLinEquiv _ K g.val)))
  (horth : ∀ u ∈ plusSp (toLinEquiv _ K g.val), ∀ w ∈ minusSp (toLinEquiv _ K g.val),
    polar (quadPlus 4 K) u w = 0)
  {P₁ P₂ : HypPair ((quadPlus 4 K).comp (plusSp (toLinEquiv _ K g.val)).subtype)}
  (h : P₁.Orth P₂) (hdim : finrank K (plusSp (toLinEquiv _ K g.val)) = 4)

theorem rhoL_comm_mk (A : SL(2, K)) :
    rhoL hc horth h hdim A * QuotientGroup.mk g = QuotientGroup.mk g * rhoL hc horth h hdim A :=
  Subgroup.mem_centralizer_singleton_iff.mp (cZero_le g (range_blockP_le_cZero g hc horth (by
    rw [range_blockP_eq g hc horth h hdim]
    exact Subgroup.mem_sup_left ⟨A, rfl⟩)))

theorem rhoR_comm_mk (B : SL(2, K)) :
    rhoR hc horth h hdim B * QuotientGroup.mk g = QuotientGroup.mk g * rhoR hc horth h hdim B :=
  Subgroup.mem_centralizer_singleton_iff.mp (cZero_le g (range_blockP_le_cZero g hc horth (by
    rw [range_blockP_eq g hc horth h hdim]
    exact Subgroup.mem_sup_right ⟨B, rfl⟩)))

end Comm

section Root

variable {T : Subgroup Y} [hTn : T.Normal] (hCT : Subgroup.centralizer (T : Set Y) = ⊥)
  (e : T ≃* StatedProj (StatedOmega (StatedQuadPlus 4 (GaloisField 3 1)))) (hzT : z ∈ T)
  (hOT : oddCoreIn (Subgroup.centralizer ({(⟨z, hzT⟩ : T)} : Set T)) = ⊥)
  (g : StatedOmega (StatedQuadPlus 4 (GaloisField 3 1))) (he : e ⟨z, hzT⟩ = QuotientGroup.mk g)
  (hg2 : toLinEquiv _ (GaloisField 3 1) g.val * toLinEquiv _ (GaloisField 3 1) g.val = 1)
  (hc : IsCompl (plusSp (toLinEquiv _ (GaloisField 3 1) g.val))
    (minusSp (toLinEquiv _ (GaloisField 3 1) g.val)))
  (horth : ∀ u ∈ plusSp (toLinEquiv _ (GaloisField 3 1) g.val),
    ∀ w ∈ minusSp (toLinEquiv _ (GaloisField 3 1) g.val),
      polar (quadPlus 4 (GaloisField 3 1)) u w = 0)
  {P₁ P₂ : HypPair ((quadPlus 4 (GaloisField 3 1)).comp
    (plusSp (toLinEquiv _ (GaloisField 3 1) g.val)).subtype)}
  (h : P₁.Orth P₂)
  (hdim : finrank (GaloisField 3 1) (plusSp (toLinEquiv _ (GaloisField 3 1) g.val)) = 4)
  {w : Fin 4 ⊕ Fin 4 → GaloisField 3 1} (hw : w ∈ minusSp (toLinEquiv _ (GaloisField 3 1) g.val))
  (hw0 : w ≠ 0) (hwQ : quadPlus 4 (GaloisField 3 1) w = 0)

include hCT hOT he hg2 hc horth h hdim hw hw0 hwQ in
theorem oddCoreIn_eq_bot_of_root : oddCoreIn (Subgroup.centralizer ({z} : Set Y)) = ⊥ := by
  set C := Subgroup.centralizer ({z} : Set Y) with hC
  set O := oddCoreIn C with hO
  have hOT' : ∀ y ∈ O, y ∈ T → y = 1 := by
    intro y hyO hyT
    set S : Subgroup T := O.comap T.subtype with hS
    have hSC : S ≤ Subgroup.centralizer ({(⟨z, hzT⟩ : T)} : Set T) := by
      intro s hs
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp (oddCoreIn_le C hs))
    have hnorm : Subgroup.centralizer ({(⟨z, hzT⟩ : T)} : Set T) ≤
        Subgroup.normalizer (S : Set T) := by
      intro c hc'
      have hcC : (c : Y) ∈ C := by
        rw [hC, Subgroup.mem_centralizer_singleton_iff]
        exact congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hc')
      rw [Subgroup.mem_normalizer_iff]
      intro s
      constructor
      · intro hs
        exact conj_mem_oddCoreIn hcC hs
      · intro hs
        have := conj_mem_oddCoreIn (C.inv_mem hcC) hs
        change (c : Y)⁻¹ * ((c : Y) * (s : Y) * (c : Y)⁻¹) * (c : Y)⁻¹⁻¹ ∈ O at this
        show (s : Y) ∈ O
        simpa [mul_assoc] using this
    have hodd : Odd (Nat.card S) := by
      have h1 : Nat.card S = Nat.card (S.map T.subtype) :=
        (Subgroup.card_map_of_injective T.subtype_injective).symm
      have h2 : S.map T.subtype ≤ O := Subgroup.map_comap_le _ _
      rw [h1]
      exact (odd_card_oddCoreIn C).of_dvd_nat (Subgroup.card_dvd_of_le h2)
    have hle := le_oddCoreIn_of_normalizes hSC hnorm hodd
    rw [hOT] at hle
    have hmem := hle (show (⟨y, hyT⟩ : T) ∈ S from hyO)
    rw [Subgroup.mem_bot] at hmem
    exact congrArg Subtype.val hmem
  have hcomm : ∀ o ∈ O, ∀ c ∈ C, c ∈ T → o * c = c * o := by
    intro o ho c hcC hcT
    have h1 : o * c * o⁻¹ * c⁻¹ ∈ O := by
      have := O.mul_mem ho (conj_mem_oddCoreIn hcC (O.inv_mem ho))
      rwa [show o * (c * o⁻¹ * c⁻¹) = o * c * o⁻¹ * c⁻¹ by group] at this
    have h2 : o * c * o⁻¹ * c⁻¹ ∈ T := T.mul_mem (hTn.conj_mem c hcT o) (T.inv_mem hcT)
    have h3 := hOT' _ h1 h2
    calc o * c = (o * c * o⁻¹ * c⁻¹) * (c * o) := by group
      _ = c * o := by rw [h3, one_mul]
  refine le_bot_iff.mp fun o ho => ?_
  set α := MulAut.congr e (MulAut.conjNormal o : MulAut T) with hα
  have hαfix : ∀ p, p * QuotientGroup.mk g = QuotientGroup.mk g * p → α p = p := by
    intro p hp
    rw [← he] at hp
    have hpz : (e.symm p : Y) * z = z * (e.symm p : Y) := by
      have := congrArg (fun q => (e.symm q : Y)) hp
      simpa using this
    exact congr_conjNormal_apply_eq e
      (hcomm o ho _ (Subgroup.mem_centralizer_singleton_iff.mpr hpz) (e.symm p).2)
  have hαodd : Odd (orderOf α) := by
    have h1 : orderOf α ∣ orderOf o :=
      orderOf_map_dvd ((MulAut.congr e).toMonoidHom.comp MulAut.conjNormal) o
    exact (odd_card_oddCoreIn C).of_dvd_nat (h1.trans (Subgroup.orderOf_dvd_natCard O ho))
  have hF := smul_eq_of_fix_block natCard_galoisField_three g hg2 hc horth h hdim hw hw0 hwQ α
    hαodd (fun A => hαfix _ (rhoL_comm_mk g hc horth h hdim A))
    (fun B => hαfix _ (rhoR_comm_mk g hc horth h hdim B))
  obtain ⟨y, hy⟩ := exists_eq_conj_of_smul_statedPointFamily α hF hαodd
  exact Subgroup.mem_bot.mpr (hOT' o ho (mem_of_congr_mem_inner hCT e ⟨y, hy.symm⟩))

include hCT hOT he hg2 hc horth h hdim hw hw0 hwQ in
theorem mem_of_root (hz : IsClassicalMember3 L z) :
    ∀ x ∈ L, (∃ k : ℕ, orderOf x = 3 ^ k) → x ∈ T := by
  have hOC := oddCoreIn_eq_bot_of_root hCT e hzT hOT g he hg2 hc horth h hdim hw hw0 hwQ
  have hOL : classicalInvolutionOddCore L = ⊥ := by
    have h1 := oddCoreIn_le_of_isSubnormal hz.subnormal
    rw [hOC, le_bot_iff] at h1
    exact (Subgroup.map_eq_bot_iff_of_injective _ L.subtype_injective).mp h1
  have eL := hz.nonempty_equiv_sl2 hOL
  set j : StatedProj (StatedOmega (StatedQuadPlus 4 (GaloisField 3 1))) →* Y :=
    T.subtype.comp e.symm.toMonoidHom with hj
  have hjinj : Function.Injective j := fun a b hab =>
    e.symm.injective (Subtype.ext hab)
  have hjz : j (QuotientGroup.mk g) = z := by
    rw [← he]
    change ((e.symm (e ⟨z, hzT⟩) : T) : Y) = z
    rw [MulEquiv.symm_apply_apply]
  have hW' : minusSp (toLinEquiv _ (GaloisField 3 1) g.val) ≠ ⊥ := fun h0 => by
    rw [h0, Submodule.mem_bot] at hw
    exact hw0 hw
  have hC : (Subgroup.centralizer ({QuotientGroup.mk g} :
      Set (StatedProj (StatedOmega (StatedQuadPlus 4 (GaloisField 3 1)))))).map j =
      T ⊓ Subgroup.centralizer ({z} : Set Y) := by
    rw [← he]
    exact map_centralizer_eq e hzT
  have hsub : ∀ R : Subgroup (StatedProj (StatedOmega (StatedQuadPlus 4 (GaloisField 3 1)))),
      IsSubnormal R (Subgroup.centralizer ({QuotientGroup.mk g} : Set _)) →
        IsSubnormal (R.map j) (Subgroup.centralizer ({z} : Set Y)) := by
    intro R hR
    have h1 := isSubnormal_map_hom j hR
    rw [hC] at h1
    exact isSubnormal_trans h1 (isSubnormal_of_normal_subgroupOf inf_le_right
      (inf_centralizer_normal T z))
  have hequiv : ∀ ρ : SL(2, GaloisField 3 1) →*
      StatedProj (StatedOmega (StatedQuadPlus 4 (GaloisField 3 1))), Function.Injective ρ →
        Nonempty (↥(ρ.range.map j) ≃* SL(2, ZMod 3)) := by
    intro ρ hρ
    obtain ⟨e₃⟩ := nonempty_mulEquiv_sl2Three_of_natCard_eq_three natCard_galoisField_three
    rw [MonoidHom.map_range]
    exact ⟨(MonoidHom.ofInjective (f := j.comp ρ) (hjinj.comp hρ)).symm.trans e₃⟩
  have hzJ : ∀ ρ : SL(2, GaloisField 3 1) →*
      StatedProj (StatedOmega (StatedQuadPlus 4 (GaloisField 3 1))),
        ρ (-1) = QuotientGroup.mk g → z ∈ ρ.range.map j := fun ρ hρ =>
    ⟨ρ (-1), ⟨-1, rfl⟩, by rw [hρ, hjz]⟩
  have hfix : ∀ ρ : SL(2, GaloisField 3 1) →*
      StatedProj (StatedOmega (StatedQuadPlus 4 (GaloisField 3 1))),
      ⁅L, ρ.range.map j⁆ = ⊥ → ∀ x ∈ L, ∀ A,
        MulAut.congr e (MulAut.conjNormal x : MulAut T) (ρ A) = ρ A := by
    intro ρ hρ x hx A
    have hm := Subgroup.commutator_mem_commutator hx
      (Subgroup.mem_map_of_mem j (MonoidHom.mem_range.mpr ⟨A, rfl⟩ : ρ A ∈ ρ.range))
    rw [hρ, Subgroup.mem_bot] at hm
    exact congr_conjNormal_apply_eq e (commutatorElement_eq_one_iff_mul_comm.mp hm)
  have hL := hsub _ (isSubnormal_rhoL_range g hc horth h hdim)
  have hR := hsub _ (isSubnormal_rhoR_range g hc horth h hdim)
  have hzL := hzJ _ (rhoL_neg_one hc horth h hdim g (fun u hu => mem_plusSp.mp hu)
    (fun w hw => mem_minusSp.mp hw))
  have hzR := hzJ _ (rhoR_neg_one hc horth h hdim g (fun u hu => mem_plusSp.mp hu)
    (fun w hw => mem_minusSp.mp hw))
  have hLT : ∀ ρ : SL(2, GaloisField 3 1) →*
      StatedProj (StatedOmega (StatedQuadPlus 4 (GaloisField 3 1))), L = ρ.range.map j →
        ∀ x ∈ L, x ∈ T := by
    intro ρ hρ x hx
    rw [hρ] at hx
    obtain ⟨p, -, rfl⟩ := hx
    exact (e.symm p).2
  rcases twinLemma3 hOC hz.subnormal hL eL (hequiv _ (rhoL_injective hc horth h hdim hW'))
    hz.orderOf_eq_two hz.mem hzL with h1 | h1
  · exact fun x hx _ => hLT _ h1 x hx
  rcases twinLemma3 hOC hz.subnormal hR eL (hequiv _ (rhoR_injective hc horth h hdim hW'))
    hz.orderOf_eq_two hz.mem hzR with h2 | h2
  · exact fun x hx _ => hLT _ h2 x hx
  intro x hx ⟨k, hk⟩
  set α := MulAut.congr e (MulAut.conjNormal x : MulAut T) with hα
  have hαodd : Odd (orderOf α) := by
    have h3 : orderOf α ∣ orderOf x :=
      orderOf_map_dvd ((MulAut.congr e).toMonoidHom.comp MulAut.conjNormal) x
    rw [hk] at h3
    exact (Odd.pow (by decide : Odd 3)).of_dvd_nat h3
  have hF := smul_eq_of_fix_block natCard_galoisField_three g hg2 hc horth h hdim hw hw0 hwQ α
    hαodd (hfix _ h1 x hx) (hfix _ h2 x hx)
  obtain ⟨y, hy⟩ := exists_eq_conj_of_smul_statedPointFamily α hF hαodd
  exact mem_of_congr_mem_inner hCT e ⟨y, hy.symm⟩

end Root

end CFSG.ClassicalInvolution.Q3.Q3T
