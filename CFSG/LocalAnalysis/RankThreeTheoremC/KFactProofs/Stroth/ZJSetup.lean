module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.ReducedChar
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.ZJ

open CFSG CFSG.Open Subgroup

variable {X : Type*} [Group X]

@[expose] def zjW (S : Subgroup X) : Subgroup X := CFSG.Quasithin.omegaOneCenterOf S

@[expose] def zjV (S : Subgroup X) : Subgroup X := normalClosure (zjW S : Set X)

theorem zjW_le (S : Subgroup X) : zjW S ≤ S :=
  CFSG.QuasithinUnique.Setup.omegaOneCenterOf_le S

theorem zjW_characteristic (S : Subgroup X) : ((zjW S).subgroupOf S).Characteristic :=
  CFSG.QuasithinUnique.Setup.characteristic_omegaOneCenterOf S

theorem zj_omegaOneCenter_le_centerOf (N : Subgroup X) :
    CFSG.Quasithin.omegaOneCenterOf N ≤ CFSG.Quasithin.centerOf N :=
  (Subgroup.closure_le _).mpr fun _ hx => hx.1

theorem zj_isElemAbelian_omegaOneCenter (N : Subgroup X) :
    CFSG.Open.IsElemAbelian 2 (CFSG.Quasithin.omegaOneCenterOf N) := by
  have hle := zj_omegaOneCenter_le_centerOf N
  have hcomm : ∀ a ∈ CFSG.Quasithin.omegaOneCenterOf N, ∀ b ∈ CFSG.Quasithin.omegaOneCenterOf N,
      a * b = b * a := fun a ha b hb =>
    Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp (hle hb)).2 a
      (Subgroup.mem_inf.mp (hle ha)).1
  refine ⟨CFSG.Quasithin.isMulCommutative_subgroup_iff.mpr hcomm, fun x hx => ?_⟩
  change x ∈ Subgroup.closure _ at hx
  induction hx using Subgroup.closure_induction with
  | mem y hy => exact hy.2
  | one => exact one_pow 2
  | mul a b ha hb iha ihb => rw [Commute.mul_pow (hcomm a ha b hb) 2, iha, ihb, one_mul]
  | inv a ha iha => rw [inv_pow, iha, inv_one]

theorem zj_conj_map_eq (N : Subgroup X) [N.Normal] (g : X) :
    N.map (MulAut.conj g).toMonoidHom = N := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact (‹N.Normal›).conj_mem z hz g
  · intro hy
    refine ⟨g⁻¹ * y * g, ?_, ?_⟩
    · have h := (‹N.Normal›).conj_mem y hy g⁻¹
      rwa [inv_inv] at h
    · show g * (g⁻¹ * y * g) * g⁻¹ = y
      group

theorem zj_omegaOneCenter_normal (N : Subgroup X) [N.Normal] :
    (CFSG.Quasithin.omegaOneCenterOf N).Normal := by
  refine ⟨fun x hx g => ?_⟩
  have hmem : (MulAut.conj g).toMonoidHom x ∈
      (CFSG.Quasithin.omegaOneCenterOf N).map (MulAut.conj g).toMonoidHom :=
    Subgroup.mem_map_of_mem _ hx
  rw [CFSG.Quasithin.omegaOneCenterOf_map_mulEquiv, zj_conj_map_eq N g] at hmem
  exact hmem

theorem zjW_le_omegaOneCenter_pCore {S : Subgroup X} (hcore : CFSG.pCore 2 X ≤ S)
    (hcent : centralizer (CFSG.pCore 2 X : Set X) ≤ CFSG.pCore 2 X) :
    zjW S ≤ CFSG.Quasithin.omegaOneCenterOf (CFSG.pCore 2 X) := by
  refine (Subgroup.closure_le _).mpr fun x hx => ?_
  have hx' : x ∈ CFSG.Quasithin.centerOf S ∧ x ^ 2 = 1 := hx
  have hxC : x ∈ centralizer (S : Set X) := (Subgroup.mem_inf.mp hx'.1).2
  have hcx : x ∈ centralizer (CFSG.pCore 2 X : Set X) :=
    Subgroup.mem_centralizer_iff.mpr fun h hh => Subgroup.mem_centralizer_iff.mp hxC h (hcore hh)
  have hmem : x ∈ CFSG.Quasithin.centerOf (CFSG.pCore 2 X) ∧ x ^ 2 = 1 :=
    ⟨Subgroup.mem_inf.mpr ⟨hcent hcx, hcx⟩, hx'.2⟩
  exact Subgroup.subset_closure hmem

theorem zjV_le_omegaOneCenter_pCore {S : Subgroup X} (hcore : CFSG.pCore 2 X ≤ S)
    (hcent : centralizer (CFSG.pCore 2 X : Set X) ≤ CFSG.pCore 2 X) :
    zjV S ≤ CFSG.Quasithin.omegaOneCenterOf (CFSG.pCore 2 X) := by
  haveI : (CFSG.Quasithin.omegaOneCenterOf (CFSG.pCore 2 X)).Normal :=
    zj_omegaOneCenter_normal (CFSG.pCore 2 X)
  unfold zjV
  refine Subgroup.normalClosure_le_normal (fun x hx => ?_)
  exact zjW_le_omegaOneCenter_pCore hcore hcent hx

instance zjV_normal (S : Subgroup X) : (zjV S).Normal := by
  unfold zjV
  exact Subgroup.normalClosure_normal

theorem zj_ne_bot_of_pCore_le [Nontrivial X] {S : Subgroup X} (hcore : CFSG.pCore 2 X ≤ S)
    (hcent : centralizer (CFSG.pCore 2 X : Set X) ≤ CFSG.pCore 2 X) : S ≠ ⊥ := by
  intro hS
  have hN : CFSG.pCore 2 X = ⊥ := le_bot_iff.mp (hS ▸ hcore)
  obtain ⟨x, hx⟩ := exists_ne (1 : X)
  apply hx
  have hxC : x ∈ centralizer (CFSG.pCore 2 X : Set X) := by
    refine Subgroup.mem_centralizer_iff.mpr fun h hh => ?_
    have h1 : h = 1 := by
      rw [SetLike.mem_coe, hN, Subgroup.mem_bot] at hh
      exact hh
    simp [h1]
  have hx1 : x ∈ CFSG.pCore 2 X := hcent hxC
  rw [hN, Subgroup.mem_bot] at hx1
  exact hx1

theorem zjW_ne_bot [Finite X] [Nontrivial X] {S : Subgroup X} (hS2 : IsPGroup 2 S)
    (hcore : CFSG.pCore 2 X ≤ S) (hcent : centralizer (CFSG.pCore 2 X : Set X) ≤ CFSG.pCore 2 X) :
    zjW S ≠ ⊥ :=
  CFSG.QuasithinUnique.Setup.omegaOneCenterOf_ne_bot hS2 (zj_ne_bot_of_pCore_le hcore hcent)

theorem zj_not_le_centralizer [Finite X] [Nontrivial X] {p : ℕ} {K S : Subgroup X}
    (hS2 : IsPGroup 2 S) (hcore : CFSG.pCore 2 X ≤ S)
    (hcent : centralizer (CFSG.pCore 2 X : Set X) ≤ CFSG.pCore 2 X)
    (hchar : ∀ Z : Subgroup X, Z ≤ S → Z ≠ ⊥ → (Z.subgroupOf S).Characteristic →
      ¬ K ≤ normalizer (Z : Set X) ⊔ CFSG.pPrimeCore p X) :
    ¬ K ≤ centralizer (zjV S : Set X) := by
  intro hK
  refine hchar (zjW S) (zjW_le S) (zjW_ne_bot hS2 hcore hcent) (zjW_characteristic S) ?_
  have hsub : (zjW S : Set X) ⊆ (zjV S : Set X) := fun x hx => Subgroup.le_normalClosure hx
  exact hK.trans ((Subgroup.centralizer_le hsub).trans
    ((Subgroup.centralizer_le_normalizer (zjW S : Set X)).trans le_sup_left))

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.ZJ
