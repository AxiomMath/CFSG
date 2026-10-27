module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactParabolicLeviSubAbstract
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockLinData
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockGroups

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

namespace KPLeviSub

open CFSG.Open Subgroup Matrix CFSG.AGLEmbedding CFSG.AGLEmbedding.LeviBlock
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {K : Type} [Field K] {n : ℕ}

section Block

variable (K n)

@[expose] noncomputable def blockEmb (I : Set ℕ) (a : Fin n) :
    ↥(linBlockSL K n I a) →* ∀ b : Fin n, GL (Fin (linBlockLen n I b)) K :=
  (MonoidHom.mulSingle (fun b : Fin n => GL (Fin (linBlockLen n I b)) K) a).comp
    (linBlockSL K n I a).subtype

@[expose] noncomputable def blockPre (I : Set ℕ) (a : Fin n) : Subgroup ↥(flagStabilizer n K I) :=
  (blockEmb K n I a).range.comap (linLeviHom K n I)

variable {K n}

theorem linLeviHom_apply_of_mem_blockPre {I : Set ℕ} {a : Fin n}
    {y : ↥(flagStabilizer n K I)} (hy : y ∈ blockPre K n I a) {b : Fin n} (hb : b ≠ a) :
    linLeviHom K n I y b = 1 := by
  classical
  obtain ⟨x, hx⟩ := hy
  rw [← hx]
  simp [blockEmb, MonoidHom.mulSingle_apply, Pi.mulSingle_eq_of_ne hb]

theorem linLeviHom_apply_mem_of_mem_blockPre {I : Set ℕ} {a : Fin n}
    {y : ↥(flagStabilizer n K I)} (hy : y ∈ blockPre K n I a) :
    linLeviHom K n I y a ∈ linBlockSL K n I a := by
  classical
  obtain ⟨x, hx⟩ := hy
  have : linLeviHom K n I y a = (x : GL (Fin (linBlockLen n I a)) K) := by
    rw [← hx]
    simp [blockEmb]
  rw [this]
  exact x.2

variable (K) in
@[expose] noncomputable def blockHom (I : Set ℕ) (a : Fin n) :
    ↥(blockPre K n I a) →* ↥(linBlockSL K n I a) :=
  ((Pi.evalMonoidHom (fun b : Fin n => GL (Fin (linBlockLen n I b)) K) a).comp
    ((linLeviHom K n I).comp (blockPre K n I a).subtype)).codRestrict (linBlockSL K n I a)
    fun y => linLeviHom_apply_mem_of_mem_blockPre y.2

abbrev blockQuot (K : Type) [Field K] (n : ℕ) (I : Set ℕ) (a : Fin n) : Type :=
  ↥(linBlockSL K n I a) ⧸ Subgroup.center ↥(linBlockSL K n I a)

theorem coe_blockHom {I : Set ℕ} {a : Fin n} (y : ↥(blockPre K n I a)) :
    ((blockHom K I a y : ↥(linBlockSL K n I a)) : GL (Fin (linBlockLen n I a)) K) =
      linLeviHom K n I (y : ↥(flagStabilizer n K I)) a := rfl

theorem blockHom_surjective (I : Set ℕ) (a : Fin n) :
    Function.Surjective (blockHom K I a) := by
  classical
  intro x
  have hmem : blockEmb K n I a x ∈ (linLeviHom K n I).range := by
    apply pi_le_range_linLeviHom
    rw [Subgroup.mem_pi]
    intro b _
    by_cases hb : b = a
    · subst hb
      simpa [blockEmb] using x.2
    · simp [blockEmb, MonoidHom.mulSingle_apply, Pi.mulSingle_eq_of_ne hb, one_mem]
  obtain ⟨q, hq⟩ := hmem
  refine ⟨⟨q, ⟨x, hq.symm⟩⟩, Subtype.ext ?_⟩
  rw [coe_blockHom, hq]
  simp [blockEmb]

theorem isPGroup_ker_blockHom [Finite K] [CharP K 2] (hn : 1 ≤ n) (I : Set ℕ) (a : Fin n) :
    IsPGroup 2 (blockHom K I a).ker := by
  classical
  have hker : ∀ y : ↥(blockPre K n I a), blockHom K I a y = 1 →
      (y : ↥(flagStabilizer n K I)) ∈ (linLeviHom K n I).ker := by
    intro y hy
    rw [MonoidHom.mem_ker]
    funext b
    by_cases hb : b = a
    · subst hb
      have := congrArg (fun z : ↥(linBlockSL K n I b) => (z : GL (Fin (linBlockLen n I b)) K)) hy
      simpa [coe_blockHom] using this
    · simpa using linLeviHom_apply_of_mem_blockPre y.2 hb
  let φ : (blockHom K I a).ker →* (linLeviHom K n I).ker :=
    (((blockPre K n I a).subtype.comp (blockHom K I a).ker.subtype)).codRestrict
      (linLeviHom K n I).ker fun y => hker y.1 y.2
  have hinj : Function.Injective φ := by
    intro y z h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun w : ↥(linLeviHom K n I).ker => ((w : ↥(flagStabilizer n K I))))
      h
  exact IsPGroup.of_injective (isPGroup_ker_linLeviHom hn) φ hinj

section Section

variable [Finite K] [CharP K 2]

theorem card_center_linBlockSL_eq {I : Set ℕ} (a : Fin n) :
    Nat.card (Subgroup.center ↥(linBlockSL K n I a)) =
      Nat.card (scalars (linBlockLen n I a) K) := by
  have h := LeviBlock.map_center_mulEquiv (slEquivToGLRange (K := K) (linBlockLen n I a))
  rw [← h, Subgroup.card_map_of_injective
    (f := (slEquivToGLRange (K := K) (linBlockLen n I a)).toMonoidHom)
    (slEquivToGLRange (K := K) (linBlockLen n I a)).injective,
    ← scalars_eq_center (linBlockLen n I a) K]

theorem card_center_linBlockSL_dvd {I : Set ℕ} (a : Fin n) (hm : 1 ≤ linBlockLen n I a) :
    Nat.card (Subgroup.center ↥(linBlockSL K n I a)) ∣ Nat.card K - 1 := by
  rw [card_center_linBlockSL_eq]
  exact card_scalars_dvd hm

theorem blockPre_scalar_eq_one {I : Set ℕ} {a : Fin n} {b : Fin n} (hba : b ≠ a)
    (hb : 1 ≤ linBlockLen n I b) {y : ↥(blockPre K n I a)}
    (hy : ((y : ↥(flagStabilizer n K I)) : SpecialLinearGroup (Fin n) K) ∈ scalars n K) :
    y = 1 := by
  obtain ⟨c, -, hc⟩ := (mem_scalars (n := n) (K := K)).1 hy
  have h1 := linLeviHom_apply_of_mem_blockPre y.2 hba
  have h2 := congrArg (fun g : GL (Fin (linBlockLen n I b)) K =>
    (g : Matrix (Fin (linBlockLen n I b)) (Fin (linBlockLen n I b)) K) ⟨0, hb⟩ ⟨0, hb⟩) h1
  simp only [coe_linLeviHom_apply, CFSG.QuasithinUnique.Vol2Native.A312L.blkAt_apply, hc,
    Matrix.scalar_apply, Matrix.diagonal_apply_eq, Units.val_one, Matrix.one_apply_eq] at h2
  have hc1 : (c : K) = 1 := h2
  have hc1' : c = 1 := Units.ext hc1
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  rw [hc, hc1', Units.val_one, map_one]
  rfl

theorem exists_levi_section_linear (hn : 1 ≤ n) (I : Set ℕ) (a : Fin n)
    (hm : 2 ≤ linBlockLen n I a) (hb : ∃ b : Fin n, b ≠ a ∧ 1 ≤ linBlockLen n I b)
    (hX : CFSG.Open.IsQuasisimple ↥(linBlockSL K n I a)) :
    ∃ Y W : Subgroup (projectiveSL n K),
      Y ≤ (flagStabilizer n K I).map (proj n K) ∧ S622IsSimpleSection Y W ∧
      W.relIndex Y = Nat.card (blockQuot K n I a) ∧
      ∀ r : ℕ, r.Prime → r ≠ 2 → ¬ r ∣ Nat.card K - 1 → ¬ r ∣ Nat.card W := by
  classical
  obtain ⟨b, hba, hbm⟩ := hb
  set ρ' : ↥(blockPre K n I a) →* projectiveSL n K :=
    ((proj n K).comp (flagStabilizer n K I).subtype).comp (blockPre K n I a).subtype with hρ'
  have hinj : Function.Injective ρ' := by
    rw [injective_iff_map_eq_one]
    intro y hy
    refine blockPre_scalar_eq_one hba hbm ?_
    have : proj n K ((y : ↥(flagStabilizer n K I)) : SpecialLinearGroup (Fin n) K) = 1 := hy
    exact (proj_eq_one_iff).1 this
  let eY : ↥(blockPre K n I a) ≃* ↥ρ'.range := MonoidHom.ofInjective hinj
  let θ : ↥(blockPre K n I a) →* blockQuot K n I a :=
    (QuotientGroup.mk' (Subgroup.center ↥(linBlockSL K n I a))).comp (blockHom K I a)
  let θ' : ↥ρ'.range →* blockQuot K n I a := θ.comp eY.symm.toMonoidHom
  have hθ' : Function.Surjective θ' :=
    ((QuotientGroup.mk'_surjective _).comp (blockHom_surjective I a)).comp eY.symm.surjective
  haveI : IsSimpleGroup (blockQuot K n I a) := hX.2
  have hsec := S622IsSimpleSection.of_surjective θ' hθ' (LeviBlock.exists_noncomm_centerQuotient hX)
  refine ⟨ρ'.range, θ'.ker.map ρ'.range.subtype, ?_, hsec, ?_, ?_⟩
  · rintro _ ⟨y, rfl⟩
    exact ⟨((y : ↥(blockPre K n I a)) : ↥(flagStabilizer n K I)).1,
      ((y : ↥(blockPre K n I a)) : ↥(flagStabilizer n K I)).2, rfl⟩
  · have h1 := Subgroup.relIndex_map_map_of_injective θ'.ker ⊤ ρ'.range.subtype_injective
    rw [Subgroup.map_top, Subgroup.range_subtype, Subgroup.relIndex_top_right] at h1
    rw [h1, Subgroup.index_ker, MonoidHom.range_eq_top.mpr hθ', Subgroup.card_top]
  · intro r hr hr2 hrK hdvd
    rw [Subgroup.card_map_of_injective ρ'.range.subtype_injective] at hdvd
    haveI : Fact r.Prime := ⟨hr⟩
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := ↥θ'.ker) r hdvd
    set w : ↥ρ'.range := z.1 with hw
    set y : ↥(blockPre K n I a) := eY.symm w with hy
    have hyker : y ∈ θ.ker := z.2
    have hordy : orderOf y = r := by
      rw [hy, MulEquiv.orderOf_eq, hw, Subgroup.orderOf_coe, hz]
    have hyc : blockHom K I a y ∈ Subgroup.center ↥(linBlockSL K n I a) :=
      (QuotientGroup.eq_one_iff _).1 (MonoidHom.mem_ker.1 hyker)
    have hyr : (blockHom K I a y) ^ r = 1 := by
      rw [← map_pow, ← hordy, pow_orderOf_eq_one, map_one]
    set u : ↥(Subgroup.center ↥(linBlockSL K n I a)) := ⟨blockHom K I a y, hyc⟩ with hu
    have hur : u ^ r = 1 := Subtype.ext (by simpa [hu] using hyr)
    have hdvd1 : orderOf u ∣ r := orderOf_dvd_of_pow_eq_one hur
    have hdvd2 : orderOf u ∣ Nat.card (Subgroup.center ↥(linBlockSL K n I a)) :=
      orderOf_dvd_natCard u
    have hdvd3 := hdvd2.trans (card_center_linBlockSL_dvd (K := K) a (by omega))
    rcases (Nat.dvd_prime hr).1 hdvd1 with h1 | h1
    · have hu1 : u = 1 := orderOf_eq_one_iff.1 h1
      have hyk : y ∈ (blockHom K I a).ker := by
        rw [MonoidHom.mem_ker]
        exact congrArg Subtype.val hu1
      obtain ⟨k, hk⟩ := isPGroup_ker_blockHom hn I a ⟨y, hyk⟩
      have hyk2 : y ^ 2 ^ k = 1 := congrArg Subtype.val hk
      have hr2k : r ∣ 2 ^ k := hordy ▸ orderOf_dvd_of_pow_eq_one hyk2
      exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 (hr.dvd_of_dvd_pow hr2k))
    · exact hrK (h1 ▸ hdvd3)

end Section

end Block

end KPLeviSub

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
