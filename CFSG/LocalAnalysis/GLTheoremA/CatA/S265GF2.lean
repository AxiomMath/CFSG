module

public import CFSG.LocalAnalysis.StandardType.GGF4TwoNTFrame
public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallExcC5F4Torus
public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallExcC5F4Orb
public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallExcC5F4Node
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264X1ExcF4Good
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.LayerComponentDvd
public import CFSG.GroupTheory.PLayer.CenterQuotientAction
public import CFSG.LocalAnalysis.GLTheoremA.P51.Quaternion
public import CFSG.LocalAnalysis.GLTheoremA.P55.Dihedral
public import CFSG.LocalAnalysis.GLTheoremA.S10.Lemma106107
public import CFSG.LocalAnalysis.GLTheoremA.S3.Lemma35
public import CFSG.LocalAnalysis.GLTheoremA.S6.Lemma62Aux

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265G

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.StandardType
open CFSG.StandardType.TableBF4TwoInputs CFSG.SeitzReduction.F4Pilot
open CFSG.StandardType.TableBF4TwoTB (tE)

private theorem map_centralizer_singleton_of_injective {G H : Type*} [Group G] [Group H] (φ : G →* H)
    (hφ : Function.Injective φ) (a : G) :
    (Subgroup.centralizer ({a} : Set G)).map φ =
      φ.range ⊓ Subgroup.centralizer ({φ a} : Set H) := by
  ext y
  simp only [Subgroup.mem_map, Subgroup.mem_inf, MonoidHom.mem_range,
    Subgroup.mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨⟨g, rfl⟩, by rw [← map_mul, ← map_mul, hg]⟩
  · rintro ⟨⟨g, rfl⟩, hy⟩
    exact ⟨g, hφ (by rw [map_mul, map_mul]; exact hy), rfl⟩

theorem glaPLayer_range_inf_centralizer_ne_bot {G H : Type*} [Group G] [Group H] [Finite G]
    [Finite H] {p : ℕ} (hp : p.Prime) (φ : G →* H) (hφ : Function.Injective φ) {x : G}
    (hx : GLAPLayer p (Subgroup.centralizer ({x} : Set G)) ≠ ⊥) :
    GLAPLayer p (φ.range ⊓ Subgroup.centralizer ({φ x} : Set H)) ≠ ⊥ := by
  have h := CFSG.glaPLayer_map_eq_of_injective hp φ hφ (Subgroup.centralizer ({x} : Set G))
  rw [map_centralizer_singleton_of_injective φ hφ] at h
  rw [← h]
  intro hbot
  exact hx ((Subgroup.map_eq_bot_iff_of_injective _ hφ).1 hbot)

theorem glaPLayer_centralizer_ne_bot_of_mulEquiv {G H : Type*} [Group G] [Group H] [Finite G]
    [Finite H] {p : ℕ} (hp : p.Prime) (α : G ≃* H) {x : G}
    (hx : GLAPLayer p (Subgroup.centralizer ({x} : Set G)) ≠ ⊥) :
    GLAPLayer p (Subgroup.centralizer ({α x} : Set H)) ≠ ⊥ := by
  have h := glaPLayer_range_inf_centralizer_ne_bot hp α.toMonoidHom α.injective hx
  rwa [MonoidHom.range_eq_top.2 α.surjective, top_inf_eq] at h

theorem glaPLayer_ne_bot_of_le_layer {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {X P : Subgroup G} (hP : P ≤ GLALayer X) (hpP : p ∣ Nat.card P) : GLAPLayer p X ≠ ⊥ := by
  obtain ⟨J, hJ, hpJ⟩ := CFSG.exists_glaPComponent_dvd_card_of_dvd_card_glaLayer hp
    (hpP.trans (Subgroup.card_dvd_of_le hP))
  intro hbot
  have hle : J ≤ GLAPLayer p X := le_sSup hJ
  rw [hbot, le_bot_iff] at hle
  rw [hle, Subgroup.card_bot] at hpJ
  exact hp.one_lt.ne' (Nat.dvd_one.1 hpJ)

section F4Two

variable
  {K : Type} [Field K] [Finite K] [CharP K 2]

theorem glaPLayer_centralizer_nodeElt (hK : Nat.card K = 2) :
    GLAPLayer 3 (Subgroup.centralizer ({nodeElt K} : Set (adjointGroup .F4 K))) ≠ ⊥ := by
  obtain ⟨-, hcomp⟩ := layer_centralizer_nodeElt (K := K) hK
  have hle : C3Levi K ≤ GLALayer (Subgroup.centralizer ({nodeElt K} : Set (adjointGroup .F4 K))) :=
    le_sSup (CFSG.Assembly.isComponentOf_iff_open.1 hcomp)
  have h3 : 3 ∣ Nat.card (C3Levi K) := by
    have h := Subgroup.card_dvd_of_le (range_torus3_le_C3Levi (K := K))
    rw [card_range_torus3] at h
    exact (dvd_pow_self 3 (by norm_num)).trans h
  exact glaPLayer_ne_bot_of_le_layer Nat.prime_three hle h3

theorem exists_glaPLayer_of_card_ge_81 (hK : Nat.card K = 2) {A : Subgroup (adjointGroup .F4 K)}
    (hA : IsElemAbelian 3 A) (h81 : 3 ^ 4 ≤ Nat.card A) :
    ∃ a ∈ A, a ≠ 1 ∧ GLAPLayer 3 (Subgroup.centralizer ({a} : Set (adjointGroup .F4 K))) ≠ ⊥ := by
  obtain ⟨c, hc⟩ := F4TwoNonToral.exists_conj_frame_of_card_F4 K hK A hA h81
  refine ⟨MulAut.conj c (nodeElt K), ?_, ?_, ?_⟩
  · rw [hc]
    exact ⟨nodeElt K, KD264Lie.X1F4.nodeElt_mem_range, rfl⟩
  · intro h1
    exact nodeElt_ne_one ((MulAut.conj c).injective (h1.trans (map_one _).symm))
  · exact glaPLayer_centralizer_ne_bot_of_mulEquiv Nat.prime_three (MulAut.conj c)
      (glaPLayer_centralizer_nodeElt hK)

theorem exists_glaPLayer_of_card_ge_27 (hK : Nat.card K = 2) {A : Subgroup (adjointGroup .F4 K)}
    (hA : IsElemAbelian 3 A) (h27 : 3 ^ 3 ≤ Nat.card A)
    (hU : ∃ U : Subgroup (adjointGroup .F4 K), U ≠ ⊥ ∧ IsPGroup 2 U ∧
      A ≤ Subgroup.normalizer (U : Set (adjointGroup .F4 K))) :
    ∃ a ∈ A, a ≠ 1 ∧ GLAPLayer 3 (Subgroup.centralizer ({a} : Set (adjointGroup .F4 K))) ≠ ⊥ := by
  obtain ⟨β, hβ⟩ := SmallExc.F4Two.exists_mulEquiv_le_range_torus3 hK hA h27 hU
  have hle : A.map β.toMonoidHom ≤ (TableBF4Two.torus3 K).range := by
    rintro _ ⟨a, ha, rfl⟩
    exact hβ a ha
  have heq : A.map β.toMonoidHom = (TableBF4Two.torus3 K).range := by
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [card_range_torus3, Subgroup.card_map_of_injective β.injective]
    exact h27
  obtain ⟨α, hα⟩ := SmallExc.F4Two.exists_mulEquiv_nodeElt_eq_vecE0 (K := K)
  have hmem : TableBF4Two.torus3 K SmallExc.F4Two.vecE0 ∈ A.map β.toMonoidHom := by
    rw [heq]
    exact ⟨_, rfl⟩
  obtain ⟨a, ha, hae⟩ := hmem
  have hγ : (α.trans β.symm) (nodeElt K) = a := by
    rw [MulEquiv.trans_apply, hα, ← hae]
    exact β.symm_apply_apply a
  refine ⟨a, ha, ?_, ?_⟩
  · intro h1
    rw [h1] at hγ
    exact nodeElt_ne_one ((α.trans β.symm).injective (hγ.trans (map_one _).symm))
  · rw [← hγ]
    exact glaPLayer_centralizer_ne_bot_of_mulEquiv Nat.prime_three (α.trans β.symm)
      (glaPLayer_centralizer_nodeElt hK)

theorem torus3_rank_data :
    IsElemAbelian 3 (TableBF4Two.torus3 K).range ∧ Nat.card (TableBF4Two.torus3 K).range = 3 ^ 3 ∧
      orderOf (TableBF4Two.rootInv K) = 2 ∧
      (TableBF4Two.torus3 K).range ≤
        Subgroup.centralizer ({TableBF4Two.rootInv K} : Set (adjointGroup .F4 K)) :=
  ⟨KD264Lie.X1F4.isElemAbelian_of_le KD264Lie.X1F4.isElemAbelian_range_tE
      KD264Lie.X1F4.range_torus3_le_range_tE, card_range_torus3,
    orderOf_eq_prime TableBF4Two.rootInv_sq TableBF4Two.rootInv_ne_one,
    SmallExc.F4Two.range_torus3_le_centralizer_rootInv⟩

theorem tE_rank_data : IsElemAbelian 3 (tE K).range ∧ Nat.card (tE K).range = 3 ^ 4 :=
  ⟨KD264Lie.X1F4.isElemAbelian_range_tE, KD264Lie.X1F4.card_range_tE⟩

end F4Two

end CFSG.LocalAnalysis.GLTheoremA.S265G

end
