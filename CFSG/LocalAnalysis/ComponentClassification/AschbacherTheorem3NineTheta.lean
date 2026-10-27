module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3NineCore
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3SmallIndexElementary

public section

namespace CFSG.ComponentClassification.AschbacherTheorem3

open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ABGLocalTools
open CFSG.Open
open scoped Pointwise

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem mem_normalizer_of_conj_le {K : Subgroup X} {y : X}
    (h1 : ∀ k ∈ K, y * k * y⁻¹ ∈ K) (h2 : ∀ k ∈ K, y⁻¹ * k * y⁻¹⁻¹ ∈ K) :
    y ∈ Subgroup.normalizer (K : Set X) := by
  refine Subgroup.mem_normalizer_iff.mpr fun k => ⟨h1 k, fun hk => ?_⟩
  have := h2 _ hk
  simpa [mul_assoc] using this

namespace Core49

variable {A T S Q H : Subgroup X}

theorem inf_normalizer_eq (c : Core49 A T S Q H) :
    S ⊓ Subgroup.normalizer (T : Set X) = T ⊔ (S ⊓ A ⊓ Subgroup.centralizer (T : Set X)) := by
  have hdec := (lemma_4_1 c.frame (c.sylowFrame.sylow.le) c.le_S).1
  rw [hdec]
  congr 1
  apply le_antisymm
  · rintro x ⟨⟨hxS, hxN⟩, hxA⟩
    refine ⟨⟨hxS, hxA⟩, Subgroup.mem_centralizer_iff.mpr fun t ht => ?_⟩
    have hcomm : x * t * x⁻¹ * t⁻¹ ∈ T ⊓ A := by
      refine ⟨?_, ?_⟩
      · exact T.mul_mem ((Subgroup.mem_normalizer_iff.mp hxN t).mp ht) (T.inv_mem ht)
      · have h1 : t * x⁻¹ * t⁻¹ ∈ A :=
          (Subgroup.mem_normalizer_iff.mp (c.frame.le_normalizer ht) _).mp (A.inv_mem hxA)
        simpa [mul_assoc] using A.mul_mem hxA h1
    rw [c.frame.inf_eq_bot, Subgroup.mem_bot] at hcomm
    calc t * x = (x * t * x⁻¹ * t⁻¹)⁻¹ * (x * t) := by group
      _ = x * t := by rw [hcomm, inv_one, one_mul]
  · rintro x ⟨⟨hxS, hxA⟩, hxC⟩
    exact ⟨⟨hxS, Subgroup.centralizer_le_normalizer _ hxC⟩, hxA⟩

theorem sylow_normalizer (c : Core49 A T S Q H) :
    IsSylowOf 2 (T ⊔ (S ⊓ A ⊓ Subgroup.centralizer (T : Set X)))
      (Subgroup.normalizer (T : Set X)) := by
  have h := c.sylowFrame.sylow_normalizer
  rwa [c.top, top_inf_eq, c.inf_normalizer_eq] at h

theorem TU_comm (c : Core49 A T S Q H) :
    IsMulCommutative (T ⊔ (S ⊓ A ⊓ Subgroup.centralizer (T : Set X)) : Subgroup X) := by
  refine isMulCommutative_sup c.elem_and_embedding.1.1 ?_ ?_
  · refine ⟨⟨fun a b => Subtype.ext ?_⟩⟩
    exact c.U_central b.2 a
  · intro t _
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    exact (c.U_central hu t).symm

theorem sylow_centralizer (c : Core49 A T S Q H) {t : X} (ht : t ∈ T) (ht1 : t ≠ 1) :
    IsSylowOf 2 (T ⊔ (S ⊓ A ⊓ Subgroup.centralizer (T : Set X))) (Subgroup.centralizer {t}) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set U := S ⊓ A ⊓ Subgroup.centralizer (T : Set X)
  have hTU2 : IsPGroup 2 (T ⊔ U : Subgroup X) :=
    c.isPGroup_S.to_le (sup_le c.le_S (inf_le_left.trans inf_le_left))
  have hTUC : T ⊔ U ≤ Subgroup.centralizer {t} := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val (c.TU_comm.is_comm.comm ⟨x, hx⟩ ⟨t, Subgroup.mem_sup_left ht⟩)
  obtain ⟨P, hP, hTUP⟩ := exists_isSylowOf_le hTU2 hTUC
  have hPH : P ≤ H := fun x hx => c.hyp43.centralizer_le c.frame ht ht1
    ⟨by rw [c.top]; exact Subgroup.mem_top _, hP.le hx⟩
  have hPN : P ≤ Subgroup.normalizer (T : Set X) :=
    c.hyp43.le_normalizer_of_le hP.isPGroup (le_sup_left.trans hTUP) hPH
  have hcard := card_le_of_isSylowOf c.sylow_normalizer hP.isPGroup hPN
  have heq : P = T ⊔ U := (Subgroup.eq_of_le_of_card_ge hTUP hcard).symm
  rw [← heq]
  exact hP

end Core49

@[expose] def gammaJoin (A T : Subgroup X) : Subgroup X :=
  ⨆ (t : X) (_ : t ∈ T) (_ : t ≠ 1), A ⊓ Subgroup.centralizer {t}

@[expose] noncomputable def thetaCore (A T : Subgroup X) : Subgroup X :=
  (CFSG.oddCore (gammaJoin A T)).map (gammaJoin A T).subtype

omit [Finite X] in
theorem gammaJoin_le (A T : Subgroup X) : gammaJoin A T ≤ A :=
  iSup_le fun _ => iSup_le fun _ => iSup_le fun _ => inf_le_left

omit [Finite X] in
theorem le_gammaJoin {A T : Subgroup X} {t : X} (ht : t ∈ T) (ht1 : t ≠ 1) :
    A ⊓ Subgroup.centralizer {t} ≤ gammaJoin A T :=
  le_iSup_of_le t (le_iSup_of_le ht (le_iSup_of_le ht1 le_rfl))

omit [Finite X] in
theorem thetaCore_le (A T : Subgroup X) : thetaCore A T ≤ gammaJoin A T :=
  Subgroup.map_subtype_le _

theorem odd_card_thetaCore (A T : Subgroup X) : Odd (Nat.card (thetaCore A T)) := by
  rw [thetaCore, Subgroup.card_map_of_injective (gammaJoin A T).subtype_injective]
  exact odd_card_oddCore _

omit [Finite X] in
theorem normalizer_gammaJoin_le (A T : Subgroup X) :
    Subgroup.normalizer ((gammaJoin A T : Subgroup X) : Set X) ≤
      Subgroup.normalizer ((thetaCore A T : Subgroup X) : Set X) := by
  have : (CFSG.oddCore (gammaJoin A T)).Characteristic := OddCore.characteristic _
  intro y hy
  exact mem_normalizer_map_of_characteristic _ hy

theorem odd_of_isSylowOf_bot {K : Subgroup X} (h : IsSylowOf 2 ⊥ K) : Odd (Nat.card K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard := h.card_eq
  rw [Subgroup.card_bot] at hcard
  have hf : (Nat.card K).factorization 2 = 0 := by
    by_contra hne
    have : 2 ≤ 2 ^ (Nat.card K).factorization 2 := Nat.le_self_pow hne 2
    omega
  rw [Nat.factorization_eq_zero_iff] at hf
  rcases hf with h1 | h1 | h1
  · exact absurd Nat.prime_two h1
  · exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp h1)
  · exact absurd h1 Nat.card_pos.ne'

namespace Core49

variable {A T S Q H : Subgroup X}

theorem gammaJoin_le_H (c : Core49 A T S Q H) : gammaJoin A T ≤ H :=
  iSup_le fun _ => iSup_le fun ht => iSup_le fun ht1 =>
    (inf_le_inf_right _ le_sup_left).trans (c.hyp43.centralizer_le c.frame ht ht1)

theorem conj_mem_U (c : Core49 A T S Q H) {y : X} (hyA : y ∈ A)
    (hyN : y ∈ Subgroup.normalizer
      ((T ⊔ (S ⊓ A ⊓ Subgroup.centralizer (T : Set X)) : Subgroup X) : Set X))
    {t : X} (ht : t ∈ T) : t⁻¹ * (y * t * y⁻¹) ∈ S ⊓ A ⊓ Subgroup.centralizer (T : Set X) := by
  set U := S ⊓ A ⊓ Subgroup.centralizer (T : Set X)
  have h1 : y * t * y⁻¹ ∈ T ⊔ U := (Subgroup.mem_normalizer_iff.mp hyN t).mp
    (Subgroup.mem_sup_left ht)
  have h2 : t⁻¹ * (y * t * y⁻¹) ∈ (T ⊔ U) ⊓ A := by
    refine ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mem_sup_left ht)) h1, ?_⟩
    have h3 : t⁻¹ * y * t⁻¹⁻¹ ∈ A :=
      (Subgroup.mem_normalizer_iff.mp (c.frame.le_normalizer (T.inv_mem ht)) _).mp hyA
    simpa [mul_assoc] using A.mul_mem h3 (A.inv_mem hyA)
  rwa [c.sup_inf_eq (inf_le_left.trans inf_le_right) (c.le_normalizer_U T)] at h2

theorem conj_gamma_le (c : Core49 A T S Q H) {y : X} (hyA : y ∈ A)
    (hyN : y ∈ Subgroup.normalizer
      ((T ⊔ (S ⊓ A ⊓ Subgroup.centralizer (T : Set X)) : Subgroup X) : Set X)) :
    ∀ g ∈ gammaJoin A T, y * g * y⁻¹ ∈ gammaJoin A T := by
  have hle : gammaJoin A T ≤ (gammaJoin A T).comap (MulAut.conj y).toMonoidHom := by
    refine iSup_le fun t => iSup_le fun ht => iSup_le fun ht1 => ?_
    rintro g ⟨hgA, hgC⟩
    have hu := c.conj_mem_U hyA hyN ht
    set u := t⁻¹ * (y * t * y⁻¹)
    have hyt : y * t * y⁻¹ = t * u := by simp [u]
    have hgt : g * t = t * g := Subgroup.mem_centralizer_singleton_iff.mp hgC
    rw [Subgroup.mem_comap]
    change y * g * y⁻¹ ∈ gammaJoin A T
    refine le_gammaJoin ht ht1 ⟨?_, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp (c.normal (Subgroup.mem_top y)) g).mp hgA
    · have hcomm : (y * g * y⁻¹) * (y * t * y⁻¹) = (y * t * y⁻¹) * (y * g * y⁻¹) := by
        calc (y * g * y⁻¹) * (y * t * y⁻¹) = y * (g * t) * y⁻¹ := by group
          _ = y * (t * g) * y⁻¹ := by rw [hgt]
          _ = (y * t * y⁻¹) * (y * g * y⁻¹) := by group
      rw [hyt] at hcomm
      have hu' := c.U_central hu (y * g * y⁻¹)
      calc (y * g * y⁻¹) * t = (y * g * y⁻¹) * (t * u) * u⁻¹ := by group
        _ = (t * u) * (y * g * y⁻¹) * u⁻¹ := by rw [hcomm]
        _ = t * (u * (y * g * y⁻¹)) * u⁻¹ := by group
        _ = t * ((y * g * y⁻¹) * u) * u⁻¹ := by rw [hu']
        _ = t * (y * g * y⁻¹) := by group
  exact fun g hg => hle hg

theorem mem_normalizer_gamma (c : Core49 A T S Q H) {y : X} (hyA : y ∈ A)
    (hyN : y ∈ Subgroup.normalizer
      ((T ⊔ (S ⊓ A ⊓ Subgroup.centralizer (T : Set X)) : Subgroup X) : Set X)) :
    y ∈ Subgroup.normalizer ((gammaJoin A T : Subgroup X) : Set X) :=
  mem_normalizer_of_conj_le (c.conj_gamma_le hyA hyN)
    (c.conj_gamma_le (A.inv_mem hyA) (Subgroup.inv_mem _ hyN))

theorem odd_QA (c : Core49 A T S Q H) : Odd (Nat.card (Q ⊓ A : Subgroup X)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsyl := c.hyp43.sylow.inf_of_le_normalizer (inf_le_left : Q ⊓ A ≤ Q)
    (fun q hq => Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer hq, c.normal (Subgroup.mem_top q)⟩)
  have hbot : T ⊓ (Q ⊓ A) = ⊥ := by
    rw [eq_bot_iff, ← c.frame.inf_eq_bot]
    exact inf_le_inf_left T inf_le_right
  rw [hbot] at hsyl
  exact odd_of_isSylowOf_bot hsyl

theorem gamma_le_normalizer_QA (c : Core49 A T S Q H) :
    gammaJoin A T ≤ Subgroup.normalizer ((Q ⊓ A : Subgroup X) : Set X) := fun g hg =>
  Subgroup.inf_normalizer_le_normalizer_inf
    ⟨c.hyp43.le_normalizer (c.gammaJoin_le_H hg), c.normal (Subgroup.mem_top g)⟩

theorem QA_le_theta (c : Core49 A T S Q H) : Q ⊓ A ≤ thetaCore A T := by
  obtain ⟨E, hET, hE4, hEel⟩ := exists_four_le c.pRank_lt
  have hEN : E ≤ Subgroup.normalizer ((Q ⊓ A : Subgroup X) : Set X) := fun e he =>
    Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer (c.hyp43.le_Q (hET he)), c.frame.le_normalizer (hET he)⟩
  have hQAΓ : Q ⊓ A ≤ gammaJoin A T :=
    le_of_centralizers_le hE4 hEel hEN c.odd_QA fun e he he1 =>
      (inf_le_inf_right _ inf_le_right).trans (le_gammaJoin (hET he) he1)
  exact le_map_oddCore hQAΓ c.gamma_le_normalizer_QA c.odd_QA

theorem Q_le (c : Core49 A T S Q H) : Q ≤ thetaCore A T ⊔ T := by
  intro q hq
  have hqX : q ∈ A ⊔ T := c.top ▸ Subgroup.mem_top q
  have hqm : q ∈ (A : Set X) * (T : Set X) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left A T c.frame.le_normalizer]
    exact hqX
  obtain ⟨a, ha, t, ht, rfl⟩ := Set.mem_mul.mp hqm
  have haQ : a ∈ Q := by simpa using Q.mul_mem hq (Q.inv_mem (c.hyp43.le_Q ht))
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (c.QA_le_theta ⟨haQ, ha⟩))
    (Subgroup.mem_sup_right ht)

omit [Finite X] in
theorem gamma_le_normalizer_theta (A T : Subgroup X) :
    gammaJoin A T ≤ Subgroup.normalizer ((thetaCore A T : Subgroup X) : Set X) := by
  intro g hg
  have : (CFSG.oddCore (gammaJoin A T)).Normal := CFSG.oddCore_normal _
  refine Subgroup.mem_normalizer_iff.mpr fun x => ⟨fun hx => ?_, fun hx => ?_⟩
  · obtain ⟨x', hx', rfl⟩ := hx
    exact ⟨⟨g, hg⟩ * x' * ⟨g, hg⟩⁻¹, this.conj_mem _ hx' _, by simp⟩
  · obtain ⟨x', hx', hxe⟩ := hx
    refine ⟨⟨g, hg⟩⁻¹ * x' * ⟨g, hg⟩⁻¹⁻¹, this.conj_mem _ hx' _, ?_⟩
    simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv, inv_inv] at hxe ⊢
    rw [hxe]
    group

theorem gamma_le_normalizer (c : Core49 A T S Q H) :
    gammaJoin A T ≤ Subgroup.normalizer ((thetaCore A T ⊔ T : Subgroup X) : Set X) := by
  have key : ∀ g ∈ gammaJoin A T, ∀ k ∈ thetaCore A T ⊔ T, g * k * g⁻¹ ∈ thetaCore A T ⊔ T := by
    intro g hg
    have hle : thetaCore A T ⊔ T ≤ (thetaCore A T ⊔ T).comap (MulAut.conj g).toMonoidHom := by
      refine sup_le ?_ ?_
      · intro k hk
        rw [Subgroup.mem_comap]
        exact Subgroup.mem_sup_left
          ((Subgroup.mem_normalizer_iff.mp (gamma_le_normalizer_theta A T hg) k).mp hk)
      · intro t ht
        rw [Subgroup.mem_comap]
        apply c.Q_le
        exact (Subgroup.mem_normalizer_iff.mp (c.hyp43.le_normalizer (c.gammaJoin_le_H hg)) t).mp
          (c.hyp43.le_Q ht)
    exact fun k hk => hle hk
  intro g hg
  exact mem_normalizer_of_conj_le (key g hg) (key g⁻¹ ((gammaJoin A T).inv_mem hg))

theorem normalizer_TU_le (c : Core49 A T S Q H) {y : X} (hyA : y ∈ A)
    (hyN : y ∈ Subgroup.normalizer
      ((T ⊔ (S ⊓ A ⊓ Subgroup.centralizer (T : Set X)) : Subgroup X) : Set X)) :
    y ∈ Subgroup.normalizer ((thetaCore A T ⊔ T ⊔ (S ⊓ A ⊓ Subgroup.centralizer (T : Set X)) :
      Subgroup X) : Set X) := by
  set U := S ⊓ A ⊓ Subgroup.centralizer (T : Set X)
  have key : ∀ z ∈ A, z ∈ Subgroup.normalizer ((T ⊔ U : Subgroup X) : Set X) →
      ∀ k ∈ thetaCore A T ⊔ T ⊔ U, z * k * z⁻¹ ∈ thetaCore A T ⊔ T ⊔ U := by
    intro z hzA hzN
    have hle : thetaCore A T ⊔ T ⊔ U ≤
        (thetaCore A T ⊔ T ⊔ U).comap (MulAut.conj z).toMonoidHom := by
      refine sup_le (sup_le ?_ ?_) ?_
      · intro k hk
        rw [Subgroup.mem_comap]
        exact Subgroup.mem_sup_left (Subgroup.mem_sup_left
          ((Subgroup.mem_normalizer_iff.mp (normalizer_gammaJoin_le A T
            (c.mem_normalizer_gamma hzA hzN)) k).mp hk))
      · intro t ht
        rw [Subgroup.mem_comap]
        have h1 : z * t * z⁻¹ ∈ T ⊔ U :=
          (Subgroup.mem_normalizer_iff.mp hzN t).mp (Subgroup.mem_sup_left ht)
        exact (sup_le (le_sup_right.trans le_sup_left) le_sup_right : T ⊔ U ≤ _) h1
      · intro u hu
        rw [Subgroup.mem_comap]
        change z * u * z⁻¹ ∈ _
        rw [c.conj_U hu z]
        exact Subgroup.mem_sup_right hu
    exact fun k hk => hle hk
  exact mem_normalizer_of_conj_le (key y hyA hyN) (key y⁻¹ (A.inv_mem hyA) (Subgroup.inv_mem _ hyN))

theorem mem_normalizer_K (c : Core49 A T S Q H) {z : X}
    (hθ : z ∈ Subgroup.normalizer ((thetaCore A T : Subgroup X) : Set X))
    (hT1 : ∀ t ∈ T, z * t * z⁻¹ ∈ thetaCore A T ⊔ T ⊔ (S ⊓ A ⊓ Subgroup.centralizer (T : Set X)))
    (hT2 : ∀ t ∈ T, z⁻¹ * t * z⁻¹⁻¹ ∈
      thetaCore A T ⊔ T ⊔ (S ⊓ A ⊓ Subgroup.centralizer (T : Set X))) :
    z ∈ Subgroup.normalizer ((thetaCore A T ⊔ T ⊔ (S ⊓ A ⊓ Subgroup.centralizer (T : Set X)) :
      Subgroup X) : Set X) := by
  set U := S ⊓ A ⊓ Subgroup.centralizer (T : Set X)
  have key : ∀ w : X, w ∈ Subgroup.normalizer ((thetaCore A T : Subgroup X) : Set X) →
      (∀ t ∈ T, w * t * w⁻¹ ∈ thetaCore A T ⊔ T ⊔ U) →
      ∀ k ∈ thetaCore A T ⊔ T ⊔ U, w * k * w⁻¹ ∈ thetaCore A T ⊔ T ⊔ U := by
    intro w hwθ hwT
    have hle : thetaCore A T ⊔ T ⊔ U ≤
        (thetaCore A T ⊔ T ⊔ U).comap (MulAut.conj w).toMonoidHom := by
      refine sup_le (sup_le ?_ ?_) ?_
      · intro k hk
        rw [Subgroup.mem_comap]
        exact Subgroup.mem_sup_left (Subgroup.mem_sup_left
          ((Subgroup.mem_normalizer_iff.mp hwθ k).mp hk))
      · intro t ht
        rw [Subgroup.mem_comap]
        exact hwT t ht
      · intro u hu
        rw [Subgroup.mem_comap]
        change w * u * w⁻¹ ∈ _
        rw [c.conj_U hu w]
        exact Subgroup.mem_sup_right hu
    exact fun k hk => hle hk
  exact mem_normalizer_of_conj_le (key z hθ hT1)
    (key z⁻¹ (Subgroup.inv_mem _ hθ) hT2)

theorem T_le_normalizer_gamma (c : Core49 A T S Q H) :
    T ≤ Subgroup.normalizer ((gammaJoin A T : Subgroup X) : Set X) := by
  have hconj : ∀ z ∈ T, ∀ g ∈ gammaJoin A T, z * g * z⁻¹ ∈ gammaJoin A T := by
    intro z hz
    have hle : gammaJoin A T ≤ (gammaJoin A T).comap (MulAut.conj z).toMonoidHom := by
      refine iSup_le fun t' => iSup_le fun ht' => iSup_le fun ht1' => ?_
      rintro g ⟨hgA, hgC⟩
      rw [Subgroup.mem_comap]
      change z * g * z⁻¹ ∈ gammaJoin A T
      have hzt : z * t' = t' * z := congrArg Subtype.val
        (c.elem_and_embedding.1.1.is_comm.comm ⟨z, hz⟩ ⟨t', ht'⟩)
      have hgt : g * t' = t' * g := Subgroup.mem_centralizer_singleton_iff.mp hgC
      refine le_gammaJoin ht' ht1' ⟨(Subgroup.mem_normalizer_iff.mp
        (c.frame.le_normalizer hz) g).mp hgA, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      have hzt' : z⁻¹ * t' * z = t' := by
        calc z⁻¹ * t' * z = z⁻¹ * (t' * z) := by group
          _ = z⁻¹ * (z * t') := by rw [hzt]
          _ = t' := by group
      calc z * g * z⁻¹ * t' = z * g * (z⁻¹ * t' * z) * z⁻¹ := by group
        _ = z * (g * t') * z⁻¹ := by rw [hzt']; group
        _ = z * (t' * g) * z⁻¹ := by rw [hgt]
        _ = (z * t' * z⁻¹) * (z * g * z⁻¹) := by group
        _ = t' * (z * g * z⁻¹) := by rw [show z * t' * z⁻¹ = t' by rw [hzt]; group]
    exact fun g hg => hle hg
  intro s hs
  exact mem_normalizer_of_conj_le (hconj s hs) (hconj s⁻¹ (T.inv_mem hs))

theorem T_le_normalizer_K (c : Core49 A T S Q H) :
    T ≤ Subgroup.normalizer ((thetaCore A T ⊔ T ⊔ (S ⊓ A ⊓ Subgroup.centralizer (T : Set X)) :
      Subgroup X) : Set X) := fun _ hz =>
  c.mem_normalizer_K (normalizer_gammaJoin_le A T (c.T_le_normalizer_gamma hz))
    (fun _ ht => Subgroup.mem_sup_left (Subgroup.mem_sup_right
      (T.mul_mem (T.mul_mem hz ht) (T.inv_mem hz))))
    (fun _ ht => Subgroup.mem_sup_left (Subgroup.mem_sup_right
      (T.mul_mem (T.mul_mem (T.inv_mem hz) ht) (T.inv_mem (T.inv_mem hz)))))

theorem gamma_le_normalizer_K (c : Core49 A T S Q H) :
    gammaJoin A T ≤ Subgroup.normalizer ((thetaCore A T ⊔ T ⊔
      (S ⊓ A ⊓ Subgroup.centralizer (T : Set X)) : Subgroup X) : Set X) := fun _ hz =>
  c.mem_normalizer_K (gamma_le_normalizer_theta A T hz)
    (fun t ht => Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.mp
      (c.gamma_le_normalizer hz) t).mp (Subgroup.mem_sup_right ht)))
    (fun t ht => Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.mp
      (c.gamma_le_normalizer ((gammaJoin A T).inv_mem hz)) t).mp (Subgroup.mem_sup_right ht)))

theorem mem_normalizer_of_conj (c : Core49 A T S Q H) {a t : X} (haA : a ∈ A) (ht : t ∈ T)
    (ht1 : t ≠ 1) (hat : a * t * a⁻¹ ∈ T ⊔ (S ⊓ A ⊓ Subgroup.centralizer (T : Set X))) :
    a ∈ Subgroup.normalizer ((thetaCore A T ⊔ T ⊔ (S ⊓ A ⊓ Subgroup.centralizer (T : Set X)) :
      Subgroup X) : Set X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set U := S ⊓ A ⊓ Subgroup.centralizer (T : Set X)
  set K := thetaCore A T ⊔ T ⊔ U
  have hu : t⁻¹ * (a * t * a⁻¹) ∈ U := by
    have h2 : t⁻¹ * (a * t * a⁻¹) ∈ (T ⊔ U) ⊓ A := by
      refine ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mem_sup_left ht)) hat, ?_⟩
      have h3 : t⁻¹ * a * t⁻¹⁻¹ ∈ A :=
        (Subgroup.mem_normalizer_iff.mp (c.frame.le_normalizer (T.inv_mem ht)) _).mp haA
      simpa [mul_assoc] using A.mul_mem h3 (A.inv_mem haA)
    rwa [c.sup_inf_eq (inf_le_left.trans inf_le_right) (c.le_normalizer_U T)] at h2
  set u := t⁻¹ * (a * t * a⁻¹)
  have hat' : a * t * a⁻¹ = t * u := by simp [u]
  set C := Subgroup.centralizer ({t} : Set X)
  have hsyl := c.sylow_centralizer ht ht1
  have haC : ∀ x ∈ C, a * x * a⁻¹ ∈ C := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff] at hx ⊢
    have hcomm : (a * x * a⁻¹) * (a * t * a⁻¹) = (a * t * a⁻¹) * (a * x * a⁻¹) := by
      calc (a * x * a⁻¹) * (a * t * a⁻¹) = a * (x * t) * a⁻¹ := by group
        _ = a * (t * x) * a⁻¹ := by rw [hx]
        _ = (a * t * a⁻¹) * (a * x * a⁻¹) := by group
    rw [hat'] at hcomm
    have hu' := c.U_central hu (a * x * a⁻¹)
    calc (a * x * a⁻¹) * t = (a * x * a⁻¹) * (t * u) * u⁻¹ := by group
      _ = (t * u) * (a * x * a⁻¹) * u⁻¹ := by rw [hcomm]
      _ = t * (u * (a * x * a⁻¹)) * u⁻¹ := by group
      _ = t * ((a * x * a⁻¹) * u) * u⁻¹ := by rw [hu']
      _ = t * (a * x * a⁻¹) := by group
  have hCa : rightConjugate C a⁻¹ = C := by
    apply Subgroup.eq_of_le_of_card_ge _ (rightConjugate_card C a⁻¹).ge
    intro x hx
    rw [mem_rightConjugate_iff, inv_inv] at hx
    have := haC _ hx
    simpa [mul_assoc] using this
  have hsyl' := isSylowOf_rightConjugate hsyl a⁻¹
  rw [hCa] at hsyl'
  obtain ⟨d, hdC, hdeq⟩ := exists_rightConjugate_eq_of_isSylowOf hsyl hsyl'
  have hyN : a⁻¹ * d ∈ Subgroup.normalizer ((T ⊔ U : Subgroup X) : Set X) := by
    rw [← rightConjugate_eq_self_iff, ← rightConjugate_mul]
    exact hdeq
  have hdecomp : ∀ x : X, ∃ t₀ ∈ T, ∃ a₀ ∈ A, x = t₀ * a₀ := by
    intro x
    have hx : x ∈ T ⊔ A := by rw [sup_comm, c.top]; exact Subgroup.mem_top x
    have hxm : x ∈ (T : Set X) * (A : Set X) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right T A c.frame.le_normalizer]
      exact hx
    obtain ⟨t₀, ht₀, a₀, ha₀, rfl⟩ := Set.mem_mul.mp hxm
    exact ⟨t₀, ht₀, a₀, ha₀, rfl⟩
  obtain ⟨t₁, ht₁, a₁, ha₁, hd⟩ := hdecomp d
  have ha₁C : a₁ ∈ A ⊓ Subgroup.centralizer {t} := by
    refine ⟨ha₁, ?_⟩
    have ht₁C : t₁⁻¹ ∈ Subgroup.centralizer ({t} : Set X) :=
      Subgroup.mem_centralizer_singleton_iff.mpr (congrArg Subtype.val
        (c.elem_and_embedding.1.1.is_comm.comm ⟨t₁⁻¹, T.inv_mem ht₁⟩ ⟨t, ht⟩))
    have := Subgroup.mul_mem _ ht₁C hdC
    rwa [hd, inv_mul_cancel_left] at this
  obtain ⟨t₂, ht₂, a₂, ha₂, hy⟩ := hdecomp (a⁻¹ * d)⁻¹
  have ha₂N : a₂ ∈ Subgroup.normalizer ((T ⊔ U : Subgroup X) : Set X) := by
    have h1 := Subgroup.mul_mem _ (Subgroup.le_normalizer
      (Subgroup.inv_mem _ (Subgroup.mem_sup_left ht₂ : t₂ ∈ T ⊔ U))) (Subgroup.inv_mem _ hyN)
    rwa [hy, inv_mul_cancel_left] at h1
  have hK₁ := c.T_le_normalizer_K ht₁
  have hK₂ := c.gamma_le_normalizer_K (le_gammaJoin ht ht1 ha₁C)
  have hK₃ := c.T_le_normalizer_K ht₂
  have hK₄ := c.normalizer_TU_le ha₂ ha₂N
  have ha : a = t₁ * a₁ * (t₂ * a₂) := by rw [← hy, ← hd]; group
  rw [ha]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hK₁ hK₂) (Subgroup.mul_mem _ hK₃ hK₄)

theorem sylow_U (c : Core49 A T S Q H) :
    IsSylowOf 2 (S ⊓ A ⊓ Subgroup.centralizer (T : Set X))
      (A ⊓ Subgroup.centralizer (T : Set X)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set U := S ⊓ A ⊓ Subgroup.centralizer (T : Set X)
  have h := c.sylow_normalizer.inf_of_le_normalizer
    (inf_le_right.trans (Subgroup.centralizer_le_normalizer _) :
      A ⊓ Subgroup.centralizer (T : Set X) ≤ Subgroup.normalizer (T : Set X))
    (fun x hx => Subgroup.inf_normalizer_le_normalizer_inf
      ⟨c.normal (Subgroup.mem_top x), normalizer_le_normalizer_centralizer _ hx⟩)
  have heq : (T ⊔ U) ⊓ (A ⊓ Subgroup.centralizer (T : Set X)) = U := by
    rw [← inf_assoc, c.sup_inf_eq (inf_le_left.trans inf_le_right) (c.le_normalizer_U T)]
    exact inf_eq_left.mpr inf_le_right
  rwa [heq] at h

theorem card_le (c : Core49 A T S Q H) {P : Subgroup X} (hPA : P ≤ A)
    (hPN : P ≤ Subgroup.normalizer
      ((T ⊔ (S ⊓ A ⊓ Subgroup.centralizer (T : Set X)) : Subgroup X) : Set X))
    (hP : IsPGroup 2 P) :
    Nat.card P ≤ Nat.card T * Nat.card (S ⊓ A ⊓ Subgroup.centralizer (T : Set X) : Subgroup X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set U := S ⊓ A ⊓ Subgroup.centralizer (T : Set X) with hUdef
  obtain ⟨hel, -⟩ := c.elem_and_embedding
  obtain ⟨t₀, ht₀1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp c.ne_bot
  have ht₀1' : (t₀ : X) ≠ 1 := fun h => ht₀1 (Subtype.ext h)
  have hmemU : ∀ y ∈ P, (t₀ : X)⁻¹ * (y⁻¹ * t₀ * y) ∈ U := by
    intro y hy
    have := c.conj_mem_U (A.inv_mem (hPA hy)) (Subgroup.inv_mem _ (hPN hy)) t₀.2
    rwa [inv_inv] at this
  let ψ : P →* X :=
    { toFun := fun y => (t₀ : X)⁻¹ * ((y : X)⁻¹ * t₀ * y)
      map_one' := by simp
      map_mul' := by
        intro a b
        have ha := hmemU a a.2
        have hb := hmemU b b.2
        have hab := c.U_central ha ((b : X)⁻¹)
        have hab' := c.U_central ha (b : X)
        simp only [Subgroup.coe_mul]
        set ua := (t₀ : X)⁻¹ * ((a : X)⁻¹ * t₀ * a)
        have h1 : (a : X)⁻¹ * t₀ * a = t₀ * ua := by simp [ua]
        calc (t₀ : X)⁻¹ * (((a : X) * b)⁻¹ * t₀ * (a * b))
            = (t₀ : X)⁻¹ * ((b : X)⁻¹ * ((a : X)⁻¹ * t₀ * a) * b) := by group
          _ = (t₀ : X)⁻¹ * ((b : X)⁻¹ * (t₀ * ua) * b) := by rw [h1]
          _ = (t₀ : X)⁻¹ * ((b : X)⁻¹ * t₀ * b) * ((b : X)⁻¹ * ua * b) := by group
          _ = (t₀ : X)⁻¹ * ((b : X)⁻¹ * t₀ * b) * ua := by
              rw [show (b : X)⁻¹ * ua * b = ua by rw [hab]; group]
          _ = ua * ((t₀ : X)⁻¹ * ((b : X)⁻¹ * t₀ * b)) := c.U_central ha _ }
  have hψ : ∀ y : P, ψ y = (t₀ : X)⁻¹ * ((y : X)⁻¹ * t₀ * y) := fun _ => rfl
  have hUab : IsMulCommutative U := ⟨⟨fun a b => Subtype.ext (c.U_central b.2 a)⟩⟩
  have hrange : ψ.range ≤ omegaOne U := by
    rintro _ ⟨y, rfl⟩
    rw [mem_omegaOne_iff hUab]
    refine ⟨hmemU y y.2, ?_⟩
    have h1 : (y : X)⁻¹ * t₀ * y = t₀ * ψ y := by rw [hψ]; group
    set u := ψ y
    have hu : u ∈ U := hmemU y y.2
    have h2 : ((y : X)⁻¹ * t₀ * y) ^ 2 = 1 := by
      rw [show ((y : X)⁻¹ * t₀ * y) ^ 2 = (y : X)⁻¹ * (t₀ : X) ^ 2 * y by
        simp only [pow_two]; group, hel.2 _ t₀.2]
      group
    rw [h1] at h2
    have hc := c.U_central hu (t₀ : X)
    calc u ^ 2 = (t₀ : X) ^ 2 * u ^ 2 := by rw [hel.2 _ t₀.2, one_mul]
      _ = ((t₀ : X) * u) ^ 2 := by
          simp only [pow_two]
          calc (t₀ : X) * t₀ * (u * u) = t₀ * (t₀ * u) * u := by group
            _ = t₀ * (u * t₀) * u := by rw [hc]
            _ = t₀ * u * (t₀ * u) := by group
      _ = 1 := h2
  have hker : (ψ.ker).map P.subtype ≤ P ⊓ Subgroup.centralizer (T : Set X) := by
    rintro _ ⟨y, hy, rfl⟩
    have hy' : ψ y = 1 := hy
    rw [hψ] at hy'
    have hy := hy'
    have hyt : (y : X)⁻¹ * t₀ * y = t₀ := by
      calc (y : X)⁻¹ * t₀ * y = (t₀ : X) * ((t₀ : X)⁻¹ * ((y : X)⁻¹ * t₀ * y)) := by group
        _ = t₀ := by rw [hy, mul_one]
    have hyA : (y : X) ∈ A := hPA y.2
    have hTy : rightConjugate T (1 : X) = rightConjugate T y := by
      apply rightConjugate_eq_of_inf_ne_bot c.sylowFrame c.hyp43 hel.1 A.one_mem hyA
      · rw [rightConjugate_one]; exact c.le_S
      · have h1 := rightConjugate_le_rightConjugate (le_sup_left : T ≤ T ⊔ U) y
        rw [(rightConjugate_eq_self_iff _ (y : X)).mpr (hPN y.2)] at h1
        exact h1.trans (sup_le c.le_S (inf_le_left.trans inf_le_left))
      · rw [rightConjugate_one]
        intro hbot
        have hmem : (t₀ : X) ∈ T ⊓ rightConjugate T y := by
          refine ⟨t₀.2, (mem_rightConjugate_iff _ _ _).mpr ?_⟩
          have : (y : X) * t₀ * (y : X)⁻¹ = t₀ := by
            calc (y : X) * t₀ * (y : X)⁻¹ = (y : X) * ((y : X)⁻¹ * t₀ * y) * (y : X)⁻¹ := by
                  rw [hyt]
              _ = t₀ := by group
          rw [this]; exact t₀.2
        rw [hbot, Subgroup.mem_bot] at hmem
        exact ht₀1' hmem
    rw [rightConjugate_one] at hTy
    have hyN : (y : X) ∈ Subgroup.normalizer (T : Set X) :=
      (rightConjugate_eq_self_iff T y).mp hTy.symm
    refine ⟨y.2, Subgroup.mem_centralizer_iff.mpr fun s hs => ?_⟩
    have hcomm : (y : X) * s * (y : X)⁻¹ * s⁻¹ ∈ T ⊓ A := by
      refine ⟨T.mul_mem ((Subgroup.mem_normalizer_iff.mp hyN s).mp hs) (T.inv_mem hs), ?_⟩
      have h1 : s * (y : X)⁻¹ * s⁻¹ ∈ A :=
        (Subgroup.mem_normalizer_iff.mp (c.frame.le_normalizer hs) _).mp (A.inv_mem hyA)
      simpa [mul_assoc] using A.mul_mem hyA h1
    rw [c.frame.inf_eq_bot, Subgroup.mem_bot] at hcomm
    calc s * (y : X) = ((y : X) * s * (y : X)⁻¹ * s⁻¹)⁻¹ * ((y : X) * s) := by group
      _ = y * s := by rw [hcomm, inv_one, one_mul]
  have hcardP := Subgroup.card_ker_mul_card_range ψ
  have hk : Nat.card ψ.ker ≤ Nat.card U := by
    have h1 : Nat.card ψ.ker = Nat.card ((ψ.ker).map P.subtype) :=
      (Subgroup.card_map_of_injective P.subtype_injective).symm
    rw [h1]
    refine (Subgroup.card_le_of_le hker).trans ?_
    refine card_le_of_isSylowOf c.sylow_U (hP.to_le inf_le_left)
      (inf_le_inf_right _ hPA)
  have hr : Nat.card ψ.range ≤ Nat.card T := by
    refine (Subgroup.card_le_of_le hrange).trans ?_
    have hΩel : Open.IsElemAbelian 2 (omegaOne U) :=
      ⟨isMulCommutative_of_le (omegaOne_le U) hUab,
        fun x hx => ((mem_omegaOne_iff hUab).mp hx).2⟩
    rw [card_eq_two_pow_pRank hΩel, card_eq_two_pow_pRank hel]
    apply Nat.pow_le_pow_right (by norm_num)
    refine (CFSG.SectionRank.pRank_mono one_lt_two ((omegaOne_le U).trans ?_)).trans c.rank
    exact le_inf c.U_le_center inf_le_right
  rw [← hcardP, mul_comm]
  exact Nat.mul_le_mul hr hk

end Core49

end CFSG.ComponentClassification.AschbacherTheorem3
