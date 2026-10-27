module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TwelveNotLeGraphProd
public import CFSG.LocalAnalysis.RankThreeTheoremC.ParabCensus.Reduce
import CFSG.LocalAnalysis.RankThreeTheoremC.ParabCensus.Assembly
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TwelveNotLeSymThreePerm
import CFSG.Open.StatedCenterThree
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TwelveNotLeDefs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TwelveNotLe.Sp

open CFSG.Open CFSG.AGLEmbedding CFSG.QuasithinUnique Subgroup

theorem pCore_eq_bot_of_isQuasisimple_of_center_eq_bot {X : Type} [Group X] [Finite X]
    (hq : Open.IsQuasisimple X) (hc : Subgroup.center X = ⊥) (p : ℕ) [Fact p.Prime] :
    CFSG.pCore p X = ⊥ := by
  let e : X ⧸ Subgroup.center X ≃* X :=
    (QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot
  haveI : IsSimpleGroup (X ⧸ Subgroup.center X) := hq.2
  haveI : IsSimpleGroup X := e.symm.isSimpleGroup
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (CFSG.pCore p X) with h | h
  · exact h
  · exfalso
    have hp : IsPGroup p (⊤ : Subgroup X) := by
      rw [← h]
      exact CFSG.pCore_isPGroup
    haveI : Group.IsNilpotent X := (hp.of_equiv Subgroup.topEquiv).isNilpotent
    haveI : Group.IsSolvable X := inferInstance
    exact (Group.IsSolvable.commutator_lt_top_of_nontrivial X).ne hq.1

theorem prodFactor_of_isSpTwoFactor {X : Type} [Group X] [Finite X]
    (h : ParabCensus.IsSpTwoFactor X) : Prod.ProdFactor X := by
  rcases h with hsub | ⟨hW, hc, -⟩ | ⟨⟨e⟩⟩
  · right
    exact ⟨eq_bot_iff.2 fun x _ => Subgroup.mem_bot.2 (Subsingleton.elim x 1),
      eq_bot_iff.2 fun x _ => Subgroup.mem_bot.2 (Subsingleton.elim x 1)⟩
  · rcases hW with ⟨hq, -⟩ | ⟨⟨e⟩⟩ | ⟨K, hK, hKfin, hK4, ⟨e⟩⟩
    · right
      exact ⟨pCore_eq_bot_of_isQuasisimple_of_center_eq_bot hq hc 2,
        pCore_eq_bot_of_isQuasisimple_of_center_eq_bot hq hc 3⟩
    · left
      exact ⟨e⟩
    · exfalso
      letI := hK
      haveI := hKfin
      have h3 : Nat.card (Subgroup.center ↥(StatedSU 3 2 K)) = 3 :=
        CFSG.Open.StatedCenterThree.card_center_statedSU_three (q := 2) (by rw [hK4]; norm_num)
          (by norm_num)
      have h1 : Nat.card (Subgroup.center X) = Nat.card (Subgroup.center ↥(StatedSU 3 2 K)) :=
        Nat.card_congr (Subgroup.centerCongr e).toEquiv
      rw [hc, Subgroup.card_bot, h3] at h1
      omega
  · right
    exact ⟨SymThree.pCore_eq_bot_of_mulEquiv 2 e (SymThree.pCore_perm_eq_bot (by norm_num) 2),
      SymThree.pCore_eq_bot_of_mulEquiv 3 e (SymThree.pCore_perm_eq_bot (by norm_num) 3)⟩

theorem exists_mem_conj_eq_of_normalizer_spTwo (hZ : OddCenterRest) {A : Type} [Group A]
    [Finite A] {Y P : Subgroup A} (hY : Open.IsQuasisimple ↥Y) (hO : pCoreOf 2 Y = ⊥)
    (hB2 : IsLieOf ParabCensus.IdxBTwo (↥Y ⧸ center ↥Y)) (hP : IsParabolicTwo Y P) {t : A}
    (htY : t ∈ normalizer (Y : Set A)) (htP : t ∈ normalizer (P : Set A)) :
    ∃ y ∈ P, ∀ w ∈ Y, t * w * t⁻¹ = y * w * y⁻¹ := by
  classical
  obtain ⟨hPY, T, hT, hTN⟩ := hP
  obtain ⟨r, K, hKfield, hKfin, hKchar, hr, hK, hψ⟩ :=
    ParabCensus.exists_mulEquiv_statedSp_of_isQuasisimple hZ hY hO hB2
  letI : Field K := hKfield
  letI : Finite K := hKfin
  letI : CharP K 2 := hKchar
  obtain ⟨ψ⟩ := hψ
  let α : MulAut ↥Y := Y.normalizerMonoidHom ⟨t, htY⟩
  have hαcoe : ∀ y : ↥Y, (α y : A) = t * (y : A) * t⁻¹ := fun y =>
    Subgroup.normalizerMonoidHom_apply_apply_coe Y ⟨t, htY⟩ y
  obtain ⟨g, hg⟩ := ParabCensus.allInner_of_mulEquiv_statedSp hr hK ψ α
  let y : A := (g : A)
  have hconj : ∀ w ∈ Y, t * w * t⁻¹ = y * w * y⁻¹ := by
    intro w hw
    have h1 : α ⟨w, hw⟩ = MulAut.conj g ⟨w, hw⟩ := by rw [hg]
    have h2 : ((α ⟨w, hw⟩ : ↥Y) : A) = t * w * t⁻¹ := hαcoe ⟨w, hw⟩
    rw [← h2, h1, MulAut.conj_apply]
    rfl
  have hyY : y ∈ Y := g.2
  have hyN : y ∈ normalizer (P : Set A) := by
    rw [Subgroup.mem_normalizer_iff]
    intro w
    constructor
    · intro hw
      have h := hconj w (hPY hw)
      rw [← h]
      exact (Subgroup.mem_normalizer_iff.mp htP w).mp hw
    · intro hw
      have hwY : w ∈ Y := by
        have h1 : y⁻¹ * (y * w * y⁻¹) * y ∈ Y :=
          Y.mul_mem (Y.mul_mem (Y.inv_mem hyY) (hPY hw)) hyY
        simpa [mul_assoc] using h1
      have h := hconj w hwY
      exact (Subgroup.mem_normalizer_iff.mp htP w).mpr (by rwa [← h] at hw)
  have hTP : T ≤ P := fun t ht => hTN ⟨hT.1 ht, le_normalizer ht⟩
  have hTP' : IsSylowTwoOf T P := by
    refine ⟨hTP, hT.2.1, ?_⟩
    intro h2
    have e : (T.subgroupOf P).index * (P.subgroupOf Y).index = (T.subgroupOf Y).index :=
      Subgroup.relIndex_mul_relIndex T P Y hTP hPY
    exact hT.2.2 (e ▸ dvd_mul_of_dvd_left h2 _)
  obtain ⟨n, hnP, hnyN⟩ :=
    CFSG.Quasithin.Vol2.Ch10.SecD.exists_mul_mem_normalizer hTP' hyN
  have hnyY : n * y ∈ Y := Y.mul_mem (hPY hnP) hyY
  have hyP : y ∈ P := by
    have h : n * y ∈ P := hTN ⟨hnyY, hnyN⟩
    have h' : n⁻¹ * (n * y) ∈ P := P.mul_mem (P.inv_mem hnP) h
    simpa using h'
  exact ⟨y, hyP, hconj⟩

theorem mem_hatOf_iff {A : Type} [Group A] {P J : Subgroup A} {x : ↥P ⧸ CFSG.pCore 2 ↥P} :
    x ∈ hatOf P J ↔ ∃ p : ↥P, (p : A) ∈ J ∧ QuotientGroup.mk' (CFSG.pCore 2 ↥P) p = x := by
  unfold hatOf
  rw [Subgroup.mem_map]
  exact ⟨fun ⟨p, hp, h⟩ => ⟨p, hp, h⟩, fun ⟨p, hp, h⟩ => ⟨p, hp, h⟩⟩

theorem hatOf_conj_eq_of_spTwo (hZ : OddCenterRest) {A : Type} [Group A] [Finite A]
    {Y P J : Subgroup A} {t : A} (hY : Open.IsQuasisimple ↥Y) (hO : pCoreOf 2 Y = ⊥)
    (hB2 : IsLieOf ParabCensus.IdxBTwo (↥Y ⧸ center ↥Y)) (hP : IsParabolicTwo Y P) (hJP : J ≤ P)
    (hJs : IsSubnormal (hatOf P J) ⊤) (hJiso : Sym.IsSymThree (hatOf P J))
    (htY : t ∈ Subgroup.normalizer (Y : Set A)) (htP : t ∈ Subgroup.normalizer (P : Set A)) :
    hatOf P (J.map (MulAut.conj t).toMonoidHom) = hatOf P J := by
  obtain ⟨y, hyP, hconj⟩ := exists_mem_conj_eq_of_normalizer_spTwo hZ hY hO hB2 hP htY htP
  obtain ⟨k, X, _, _, ⟨e⟩, hX⟩ := ParabCensus.isSpTwoLeviProduct_of_parabolic hZ hY hO hB2 hP
  have hnorm : (hatOf P J).Normal :=
    Prod.normal_of_subnormal_symThree_of_equiv (fun i => prodFactor_of_isSpTwoFactor (hX i)) e
      hJiso hJs
  have hyJ : ∀ j ∈ J, j ∈ Y := fun j hj => hP.1 (hJP hj)
  have hmap : J.map (MulAut.conj t).toMonoidHom = J.map (MulAut.conj y).toMonoidHom := by
    ext x
    simp only [Subgroup.mem_map]
    constructor <;> rintro ⟨j, hj, rfl⟩ <;> refine ⟨j, hj, ?_⟩ <;>
      simp [MulAut.conj_apply, hconj j (hyJ j hj)]
  rw [hmap]
  let yP : ↥P := ⟨y, hyP⟩
  ext x
  constructor
  · intro hx
    obtain ⟨p, ⟨j, hj, hjp⟩, rfl⟩ := mem_hatOf_iff.1 hx
    have hjP : j ∈ P := hJP hj
    have hpeq : p = yP * ⟨j, hjP⟩ * yP⁻¹ :=
      Subtype.ext (by simpa [yP, MulAut.conj_apply] using hjp.symm)
    have hjmem : QuotientGroup.mk' (CFSG.pCore 2 ↥P) ⟨j, hjP⟩ ∈ hatOf P J :=
      mem_hatOf_iff.2 ⟨⟨j, hjP⟩, hj, rfl⟩
    have h := hnorm.conj_mem _ hjmem (QuotientGroup.mk' (CFSG.pCore 2 ↥P) yP)
    rw [hpeq, map_mul, map_mul, map_inv]
    exact h
  · intro hx
    obtain ⟨p, hp, rfl⟩ := mem_hatOf_iff.1 hx
    have h := hnorm.conj_mem _ hx (QuotientGroup.mk' (CFSG.pCore 2 ↥P) yP)⁻¹
    obtain ⟨p', hp', hqp'⟩ := mem_hatOf_iff.1 h
    refine mem_hatOf_iff.2 ⟨yP * p' * yP⁻¹, ⟨p', hp', ?_⟩, ?_⟩
    · simp [yP, MulAut.conj_apply]
    · rw [map_mul, map_mul, map_inv, hqp']
      group

end CFSG.LocalAnalysis.RankThreeTheoremC.TwelveNotLe.Sp
