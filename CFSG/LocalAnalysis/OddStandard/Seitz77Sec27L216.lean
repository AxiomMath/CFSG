module

public import CFSG.LocalAnalysis.OddStandard.Seitz77Sec27HaradaLocal
public import CFSG.LocalAnalysis.OddStandard.Seitz77Sec27StructAux
public import CFSG.GH74.Uniqueness.SU.KI1r4F61L216
public import Certificates.Data.Seitz77Sec27L216

public section

namespace CFSG.OddStandard.Seitz77

open Subgroup CFSG.Blueprint CFSG.GH74.KGroups CFSG.GH74.Uniqueness.SU.K.R4.L216M

theorem card_centralizer_model {N : Type} [Group N] {K : Subgroup N} [K.Normal] {G : Type}
    [Group G] (M : AutModel ↥K G) (t : N) :
    Nat.card ↥(centralizer ({t} : Set N) ⊓ K) =
      Nat.card ↥(centralizer ({(M.Φ (MulAut.conjNormal t) : G)} : Set G) ⊓ M.P) := by
  obtain ⟨φ, hφ⟩ : ∃ φ : MulAut ↥K, φ = MulAut.conjNormal t := ⟨_, rfl⟩
  rw [← hφ]
  obtain ⟨τ, hτ⟩ : ∃ τ : G, τ = (M.Φ φ : G) := ⟨_, rfl⟩
  rw [← hτ]
  have key : ∀ k : ↥K, ((k : N) ∈ centralizer ({t} : Set N)) ↔
      (((M.e k : M.P) : G) ∈ centralizer ({τ} : Set G)) := by
    intro k
    rw [mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
    have h1 : (k : N) * t = t * (k : N) ↔ φ k = k := by
      rw [← Subtype.coe_inj, hφ, MulAut.conjNormal_apply, mul_inv_eq_iff_eq_mul]
      exact eq_comm
    have h2 : φ k = k ↔ M.e (φ k) = M.e k := M.e.injective.eq_iff.symm
    have h3 : M.e (φ k) = M.e k ↔ τ * ((M.e k : M.P) : G) = ((M.e k : M.P) : G) * τ := by
      rw [← Subtype.coe_inj, M.spec φ k, ← hτ, mul_inv_eq_iff_eq_mul]
    rw [h1, h2, h3]
    exact eq_comm
  let e₁ : ↥(centralizer ({t} : Set N) ⊓ K) ≃ {k : ↥K // (k : N) ∈ centralizer ({t} : Set N)} :=
    { toFun := fun x => ⟨⟨x.1, (mem_inf.1 x.2).2⟩, (mem_inf.1 x.2).1⟩
      invFun := fun k => ⟨k.1.1, mem_inf.2 ⟨k.2, k.1.2⟩⟩
      left_inv := fun x => rfl
      right_inv := fun k => rfl }
  let e₄ : {p : M.P // (p : G) ∈ centralizer ({τ} : Set G)} ≃
      ↥(centralizer ({τ} : Set G) ⊓ M.P) :=
    { toFun := fun p => ⟨p.1.1, mem_inf.2 ⟨p.2, p.1.2⟩⟩
      invFun := fun y => ⟨⟨y.1, (mem_inf.1 y.2).2⟩, (mem_inf.1 y.2).1⟩
      left_inv := fun p => rfl
      right_inv := fun y => rfl }
  exact Nat.card_congr
    (((e₁.trans (Equiv.subtypeEquivRight key)).trans
      (M.e.toEquiv.subtypeEquiv fun k => Iff.rfl)).trans e₄)

theorem card_centralizer_QP (t : Equiv.Perm (Fin 17)) :
    Nat.card ↥(centralizer ({t} : Set (Equiv.Perm (Fin 17))) ⊓ QP.originalSubgroup) =
      Certificates.Seitz77Sec27.l216CommCount (elemsT QP) t := by
  have h := card_filter QP QP_ok (fun g : Equiv.Perm (Fin 17) => g * t = t * g)
  refine Eq.trans (Nat.card_congr ?_) (h.trans rfl)
  exact
    { toFun := fun x =>
        ⟨⟨x.1, (mem_inf.1 x.2).2⟩, mem_centralizer_singleton_iff.1 (mem_inf.1 x.2).1⟩
      invFun := fun g => ⟨g.1.1, mem_inf.2 ⟨mem_centralizer_singleton_iff.2 g.2, g.1.2⟩⟩
      left_inv := fun x => rfl
      right_inv := fun g => rfl }

theorem l216CensusCheck_spec
    (h : Certificates.Seitz77Sec27.l216CensusCheck = true) :
    ∀ t ∈ QA.originalSubgroup, t * t = 1 → t ≠ 1 →
      (t ∈ QP.originalSubgroup → Nat.card ↥(centralizer ({t} : Set (Equiv.Perm (Fin 17))) ⊓ QP.originalSubgroup) = 16) ∧
      (t ∉ QP.originalSubgroup → Nat.card ↥(centralizer ({t} : Set (Equiv.Perm (Fin 17))) ⊓ QP.originalSubgroup) = 60) := by
  intro t ht ht2 ht1
  have hall := forall_of_all QA QA_ok (p := fun t => !(decide (t * t = 1) && decide (t ≠ 1)) ||
    (if t ∈ elemsT QP then Certificates.Seitz77Sec27.l216CommCount (elemsT QP) t == 16
      else Certificates.Seitz77Sec27.l216CommCount (elemsT QP) t == 60)) h t ht
  simp only [Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff,
    decide_eq_false_iff_not] at hall
  rcases hall with h1 | h1
  · exact absurd ht2 (by simpa [ht1] using h1)
  · refine ⟨fun hP => ?_, fun hP => ?_⟩
    · rw [card_centralizer_QP]
      have hmem : t ∈ elemsT QP := (mem_elemsT QP QP_ok t).2 hP
      simpa [hmem] using h1
    · rw [card_centralizer_QP]
      have hmem : t ∉ elemsT QP := fun h => hP ((mem_elemsT QP QP_ok t).1 h)
      simpa [hmem] using h1

theorem caseAL216
    (hcheck : Certificates.Seitz77Sec27.l216CensusCheck = true) : CaseAL216 := by
  intro N _ _ X t o h
  have hchar : (layer N).Characteristic := CFSG.LocalCores.layer_characteristic
  obtain ⟨M, hMP, hMA⟩ := autModel h
  have hcensus := l216CensusCheck_spec hcheck
  have hinj := conjNormal_injective_of_centralizer_eq_bot (K := layer N) o.cent_bot
  have ht1 : t ≠ 1 := by
    intro h1
    have := o.loc.t_order
    rw [h1, orderOf_one] at this
    omega
  set τ : Equiv.Perm (Fin 17) := (M.Φ (MulAut.conjNormal t) : Equiv.Perm (Fin 17)) with hτ
  have hτA : τ ∈ QA.originalSubgroup := hMA ▸ (M.Φ _).2
  have hτ2 : τ * τ = 1 := by
    have h2 : (MulAut.conjNormal t : MulAut ↥(layer N)) ^ 2 = 1 := by
      rw [← map_pow, sq, o.loc.t_mul_t, map_one]
    have := M.Φ_pow (MulAut.conjNormal t) 2
    rw [h2, M.Φ_one] at this
    rw [hτ, ← sq]
    exact this.symm
  have hτ1 : τ ≠ 1 := by
    intro h1
    exact ht1 (hinj ((M.Φ_eq_one).1 h1 |>.trans (map_one _).symm))
  have hcard := card_centralizer_model M t
  rw [hMP] at hcard
  obtain ⟨hin, hout⟩ := hcensus τ hτA hτ2 hτ1
  have hXle : X ≤ centralizer ({t} : Set N) ⊓ layer N :=
    le_inf o.loc.X_le_centralizer_t o.X_le
  by_cases hτP : τ ∈ QP.originalSubgroup
  · exfalso
    have h16 := hin hτP
    rw [← hcard] at h16
    have h60 : 60 ∣ 16 := by
      rw [← o.loc.card_eq_sixty, ← h16]
      exact Subgroup.card_dvd_of_le hXle
    norm_num at h60
  · have h60 := hout hτP
    rw [← hcard] at h60
    have hXeq : X = centralizer ({t} : Set N) ⊓ layer N :=
      Subgroup.eq_of_le_of_card_ge hXle (by rw [h60, o.loc.card_eq_sixty])
    refine ⟨h, fun htL => o.loc.t_not_mem_X ?_, hXeq⟩
    rw [hXeq]
    exact ⟨mem_centralizer_singleton_iff.2 rfl, htL⟩

end CFSG.OddStandard.Seitz77
