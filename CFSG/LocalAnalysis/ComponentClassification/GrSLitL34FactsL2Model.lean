module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsL2Cert
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsCyclicCenterModelBase
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsUnbalInner

public section

namespace CFSG.ComponentClassification.GrSLit.L34Facts

open CFSG Subgroup CFSG.GH74.KGroups Equiv
open CFSG.ComponentClassification.UnbalancedLayer

variable {G : Type} [Group G] {J : Subgroup G}

theorem exists_l2Model
    (h : IsL2Type 5 (Jhat J) ∨ IsL2Type 7 (Jhat J)) :
    ∃ (n : ℕ) (M : AutModel (Jhat J) (Perm (Fin n))), L2ModelFacts M.P M.A := by
  rcases h with h5 | h7
  · obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := GSThmB.statedClassicalModel_of_lieModel_ne_zero
      (by norm_num) h5
    obtain ⟨e'⟩ := CFSG.ClassicalModels.nonempty_statedLinearModel_equiv_alternating_five F
      (Or.inr (by simpa using hF))
    have hbij := GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 5 (by norm_num)
      (by norm_num)
    let Φ' : (⊤ : Subgroup (Perm (Fin 5))) ≃* MulAut (alternatingGroup (Fin 5)) :=
      topEquiv.trans (MulEquiv.ofBijective _ hbij)
    refine ⟨5, AutModel.ofRealization (alternatingGroup (Fin 5)) ⊤ (e.trans e') Φ'
      (fun σ x => by
        show ((MulAut.conjNormal (σ : Perm (Fin 5)) x : alternatingGroup (Fin 5)) :
          Perm (Fin 5)) = σ * x * (σ : Perm (Fin 5))⁻¹
        rw [MulAut.conjNormal_apply]), a5Facts⟩
  · obtain ⟨e⟩ := L27.equiv_of_lieModel h7
    obtain ⟨M, hP, hA⟩ := L27.autModel e
    exact ⟨8, M, hP ▸ hA ▸ l27Facts⟩

variable {n : ℕ} (M : AutModel (Jhat J) (Perm (Fin n)))

@[expose] noncomputable def rhoM {g : G} (hg : g ∈ normalizer (J : Set G)) : Perm (Fin n) :=
  (M.Φ (betaHat J hg) : Perm (Fin n))

theorem rhoM_mem {g : G} (hg : g ∈ normalizer (J : Set G)) : rhoM M hg ∈ M.A :=
  (M.Φ (betaHat J hg)).2

theorem rhoM_spec {g : G} (hg : g ∈ normalizer (J : Set G)) (k : Jhat J) :
    ((M.e (betaHat J hg k) : M.P) : Perm (Fin n)) =
      rhoM M hg * (M.e k : Perm (Fin n)) * (rhoM M hg)⁻¹ :=
  M.spec _ k

theorem rhoM_mul {g h : G} (hg : g ∈ normalizer (J : Set G)) (hh : h ∈ normalizer (J : Set G)) :
    rhoM M (mul_mem hg hh) = rhoM M hh * rhoM M hg := by
  have h1 : betaHat J (mul_mem hg hh) = betaHat J hh * betaHat J hg :=
    MulEquiv.ext fun e => betaHat_mul J hg hh e
  rw [rhoM, rhoM, rhoM, h1, map_mul, Subgroup.coe_mul]

theorem rhoM_congr {g h : G} (hg : g ∈ normalizer (J : Set G)) (hh : h ∈ normalizer (J : Set G))
    (hgh : g = h) : rhoM M hg = rhoM M hh := by
  subst hgh
  rfl

theorem rhoM_eq_one {g : G} (hg : g ∈ normalizer (J : Set G)) (h1 : rhoM M hg = 1) :
    ∀ e, betaHat J hg e = e := by
  have h2 : M.Φ (betaHat J hg) = 1 := Subtype.ext h1
  rw [map_eq_one_iff _ M.Φ.injective] at h2
  intro e
  rw [h2]
  rfl

theorem rhoM_one {g : G} (hg : g ∈ normalizer (J : Set G)) (h1 : g = 1) : rhoM M hg = 1 := by
  have h2 : betaHat J hg = 1 := MulEquiv.ext fun e => betaHat_eq_self J hg h1 e
  rw [rhoM, h2, map_one]
  rfl

theorem rhoM_pow {g : G} (hg : g ∈ normalizer (J : Set G)) (k : ℕ) :
    rhoM M (pow_mem hg k) = rhoM M hg ^ k := by
  induction k with
  | zero => exact rhoM_one M _ (pow_zero g)
  | succ k ih =>
    rw [rhoM_congr M (pow_mem hg (k + 1)) (mul_mem (pow_mem hg k) hg) (pow_succ g k),
      rhoM_mul M (pow_mem hg k) hg, ih, pow_succ']

theorem rhoM_comm {g h : G} (hg : g ∈ normalizer (J : Set G)) (hh : h ∈ normalizer (J : Set G))
    (hgh : g * h = h * g) : rhoM M hg * rhoM M hh = rhoM M hh * rhoM M hg := by
  rw [← rhoM_mul, ← rhoM_mul]
  exact rhoM_congr M _ _ hgh.symm

theorem comm_mem_oddIn_of_rhoM {g : G} (hg : g ∈ normalizer (J : Set G)) (h1 : rhoM M hg = 1)
    {j : G} (hj : j ∈ J) : j⁻¹ * g⁻¹ * j * g ∈ oddIn J := by
  have hmem : j⁻¹ * g⁻¹ * j * g ∈ J := by
    have := conj_mem_of_mem_normalizer hg hj
    rw [show j⁻¹ * g⁻¹ * j * g = j⁻¹ * (g⁻¹ * j * g) by group]
    exact J.mul_mem (J.inv_mem hj) this
  rw [mem_oddIn_iff hmem]
  have e1 : (⟨j⁻¹ * g⁻¹ * j * g, hmem⟩ : J) = (⟨j, hj⟩ : J)⁻¹ * conjJ J hg ⟨j, hj⟩ := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_conjJ]
    group
  rw [e1, map_mul, map_inv, ← betaHat_jq, rhoM_eq_one M hg h1, inv_mul_cancel]

theorem false_of_closure_le_oddIn (hF : L2ModelFacts M.P M.A) {X : Set G}
    (h : closure {y | ∃ j ∈ J, ∃ d ∈ X, y = j⁻¹ * d⁻¹ * j * d} = J)
    (hX : ∀ d ∈ X, ∀ j ∈ J, j⁻¹ * d⁻¹ * j * d ∈ oddIn J) : False := by
  have hle : J ≤ oddIn J := by
    intro y hy
    rw [← h] at hy
    refine (closure_le (oddIn J)).2 ?_ hy
    rintro _ ⟨j, hj, d, hd, rfl⟩
    exact hX d hd j hj
  obtain ⟨y, hyP, hy1⟩ := hF.ntriv
  obtain ⟨k, hk⟩ := M.e.surjective ⟨y, hyP⟩
  obtain ⟨j, rfl⟩ := jq_surjective J k
  have h1 := (mem_oddIn_iff j.2).1 (hle j.2)
  have e1 : (⟨(j : G), j.2⟩ : J) = j := rfl
  rw [e1] at h1
  rw [h1, map_one] at hk
  exact hy1 (congrArg Subtype.val hk).symm

variable [Finite G]

theorem rhoM_outer (hF : L2ModelFacts M.P M.A) {x : G} (hxN : x ∈ normalizer (J : Set G))
    (hx2 : x * x = 1)
    (hxJ : closure {y | ∃ j ∈ J, ∃ d ∈ ({x} : Set G), y = j⁻¹ * d⁻¹ * j * d} = J) {D : Set G}
    (hDJ : closure {y | ∃ j ∈ J, ∃ d ∈ D, y = j⁻¹ * d⁻¹ * j * d} = J)
    (hDo : ∀ d ∈ D, d ∈ (pPrimeCore 2 (centralizer ({x} : Set G))).map
      (centralizer ({x} : Set G)).subtype) :
    rhoM M hxN * rhoM M hxN = 1 ∧ rhoM M hxN ≠ 1 ∧ rhoM M hxN ∉ M.P := by
  have h2 : rhoM M hxN * rhoM M hxN = 1 := by
    rw [← rhoM_mul M hxN hxN]
    exact rhoM_one M _ hx2
  have h1 : rhoM M hxN ≠ 1 := fun h => false_of_closure_le_oddIn M hF hxJ fun d hd j hj => by
    rw [Set.mem_singleton_iff] at hd
    subst hd
    exact comm_mem_oddIn_of_rhoM M hxN h hj
  refine ⟨h2, h1, fun hP => ?_⟩
  have hDN := fun d (hd : d ∈ D) => mem_normalizer_of_closure hDJ hd
  refine false_of_closure_le_oddIn M hF hDJ fun d hd j hj => ?_
  have hxd : x * d = d * x :=
    (mem_centralizer_singleton_iff.mp (mem_centralizer_of_mem_oddCore (hDo d hd))).symm
  have hc := rhoM_comm M hxN (hDN d hd) hxd
  have h16 := hF.inner _ hP h2 h1 _ (rhoM_mem M (hDN d hd)) hc.symm
  have hpow : rhoM M (hDN d hd) ^ orderOf d = 1 := by
    rw [← rhoM_pow M (hDN d hd)]
    exact rhoM_one M _ (pow_orderOf_eq_one d)
  have hodd : Nat.Coprime 2 (orderOf (rhoM M (hDN d hd))) :=
    (coprime_orderOf_of_mem_oddCore (hDo d hd)).coprime_dvd_right
      (orderOf_dvd_of_pow_eq_one hpow)
  have hρ1 : rhoM M (hDN d hd) = 1 := eq_one_of_coprime_of_pow (k := 4) hodd (by
    rw [show (2 : ℕ) ^ 4 = 16 by norm_num]
    exact h16)
  exact comm_mem_oddIn_of_rhoM M (hDN d hd) hρ1 hj

theorem elemTwo_card_le_four {F : Subgroup G} (h2 : ∀ f ∈ F, f * f = 1)
    (hrk : pRank 2 ↥F ≤ 2) : IsElemTwo F ∧ Nat.card F ≤ 4 := by
  have hF : IsElemTwo F := ⟨fun u hu v hv => comm_of_mul_self (h2 u hu) (h2 v hv)
    (h2 _ (mul_mem hu hv)), h2⟩
  refine ⟨hF, ?_⟩
  by_contra hlt
  push Not at hlt
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨r, hr⟩ := (IsPGroup.iff_card (p := 2) (G := ↥F)).mp hF.isPGroup
  have h8 : 8 ≤ Nat.card F := by
    rw [hr] at hlt ⊢
    rcases Nat.lt_or_ge r 3 with h | h
    · interval_cases r <;> simp at hlt
    · calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ r := Nat.pow_le_pow_right (by norm_num) h
  have := hF.three_le_pRank h8
  omega

theorem four_l2 (hF : L2ModelFacts M.P M.A) {x : G} (hxN : x ∈ normalizer (J : Set G))
    (hρ : rhoM M hxN * rhoM M hxN = 1 ∧ rhoM M hxN ≠ 1 ∧ rhoM M hxN ∉ M.P) {F : Subgroup G}
    (hFN : F ≤ normalizer (J : Set G) ⊓ centralizer ({x} : Set G)) (hF2 : IsPGroup 2 F)
    (hFK : F ⊓ coreActionKernel J = ⊥) (hrk : pRank 2 ↥F ≤ 2) :
    IsElemTwo F ∧ Nat.card F ≤ 4 := by
  refine elemTwo_card_le_four (fun f hf => ?_) hrk
  obtain ⟨hfN, hfx⟩ := mem_inf.mp (hFN hf)
  have hc := rhoM_comm M hxN hfN (mem_centralizer_singleton_iff.mp hfx).symm
  obtain ⟨k, hk⟩ := hF2 ⟨f, hf⟩
  have hfk : f ^ 2 ^ k = 1 := congrArg Subtype.val hk
  have hρk : rhoM M hfN ^ 2 ^ k = 1 := by
    rw [← rhoM_pow M hfN]
    exact rhoM_one M _ hfk
  have h16 := hF.two _ (rhoM_mem M hfN) k hρk
  have hsq := hF.outer2 _ (rhoM_mem M hxN) hρ.1 hρ.2.1 hρ.2.2 _ (rhoM_mem M hfN) hc.symm h16
  have hff : rhoM M (mul_mem hfN hfN) = 1 := by rw [rhoM_mul M hfN hfN]; exact hsq
  have hK : f * f ∈ coreActionKernel J :=
    mem_coreActionKernel.mpr ⟨mul_mem hfN hfN, fun j hj =>
      comm_mem_oddIn_of_rhoM M (mul_mem hfN hfN) hff hj⟩
  have hmem : f * f ∈ F ⊓ coreActionKernel J := mem_inf.mpr ⟨mul_mem hf hf, hK⟩
  rw [hFK, mem_bot] at hmem
  exact hmem

end CFSG.ComponentClassification.GrSLit.L34Facts
