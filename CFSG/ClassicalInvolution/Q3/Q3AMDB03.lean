module

public import CFSG.ClassicalInvolution.Q3.Q3AMDB02
public import CFSG.ClassicalInvolution.Q3.Q3CHS2Tri

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3AM

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Uniform CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Q3.Q3T8.Asc77 CFSG.ClassicalInvolution.Q3.Q3NL
  CFSG.ClassicalInvolution.Q3.Q3CP

section Elementary

variable {G : Type} [Group G]

theorem isSylow2In_top_of_sylow (S : Sylow 2 G) : IsSylow2In (S : Subgroup G) ⊤ :=
  ⟨le_top, S.isPGroup', fun _ _ hV2 hle => S.is_maximal' hV2 hle⟩

theorem exists_sylow_of_isSylow2In_top {P : Subgroup G} (h : IsSylow2In P ⊤) :
    ∃ S : Sylow 2 G, (S : Subgroup G) = P :=
  ⟨{ toSubgroup := P
     isPGroup' := h.2.1
     is_maximal' := fun hQ hle => h.2.2 _ le_top hQ hle }, rfl⟩

theorem exists_isSylow2In_top_between [Finite G] {z : G} {P₀ : Subgroup G}
    (hP₀ : IsSylow2In P₀ ⊤) (hP₀z : P₀ ≤ Subgroup.centralizer ({z} : Set G)) {E : Subgroup G}
    (hE : IsPGroup 2 E) (hEz : E ≤ Subgroup.centralizer ({z} : Set G)) :
    ∃ P : Subgroup G, IsSylow2In P ⊤ ∧ P ≤ Subgroup.centralizer ({z} : Set G) ∧ E ≤ P := by
  obtain ⟨V, hV, hEV⟩ := IsSylow2In.exists_ge hE hEz
  have hP₀C : IsSylow2In P₀ (Subgroup.centralizer ({z} : Set G)) :=
    ⟨hP₀z, hP₀.2.1, fun V' hV'M hV'2 hle => hP₀.2.2 V' le_top hV'2 hle⟩
  obtain ⟨c, -, hcV⟩ :=
    Disconnected.AschTight.Sec6Gen.exists_conjSub_eq_of_isSylow2In hP₀C hV
  refine ⟨V, ?_, hV.1, hEV⟩
  rw [← hcV]
  exact isSylow2In_top_conj hP₀ c

end Elementary

section Central


variable {G : Type} [Group G] [Finite G]

theorem PspSetting.exists_isSylow2In_centralizer [IsSimpleGroup G] {Ω : Set (Subgroup G)}
    {K J K' : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}
    (hset : PspSetting Ω K J S R T W z t K') :
    ∃ P : Subgroup G, IsSylow2In P ⊤ ∧ P ≤ Subgroup.centralizer ({z} : Set G) ∧
      Subgroup.closure ({z, t} : Set G) ≤ P := by
  have hbad := hset.bad
  have hstd := hbad.std
  have hΩ : HypOmegaMod Ω := hstd.stand.hyp
  have hu := hset.uniq_mul
  have hzt := hset.mul_comm_zt
  obtain ⟨t₁, t₂, t₃, R₁, R₂, R₃, hax⟩ := hbad.exists_axis_of_triangle hset.intrinsic
    hstd.stand.mem hstd.hJ hset.nbrK hset.nbrJ hstd.hz hstd.ht hu rfl
  have hP : IsPGroup 2 ↥(R₁ ⊔ R₂ ⊔ R₃) := by
    have h12 := Q3CH.isPGroup_sup_of_commute hax.syl₁.2.1 hax.syl₂.2.1 hax.comm₁₂
    refine Q3CH.isPGroup_sup_of_commute h12 hax.syl₃.2.1 fun a ha b hb => ?_
    have hle : R₁ ⊔ R₂ ≤ Subgroup.centralizer (R₃ : Set G) :=
      sup_le (fun x hx => Subgroup.mem_centralizer_iff.mpr fun y hy =>
          (hax.comm₁₃ x hx y hy).symm)
        (fun x hx => Subgroup.mem_centralizer_iff.mpr fun y hy =>
          (hax.comm₂₃ x hx y hy).symm)
    exact ((Subgroup.mem_centralizer_iff.mp (hle ha)) b hb).symm
  obtain ⟨S₀, hPS⟩ := hP.exists_le_sylow
  have h₁S : R₁ ≤ (S₀ : Subgroup G) := le_sup_left.trans (le_sup_left.trans hPS)
  have h₂S : R₂ ≤ (S₀ : Subgroup G) := le_sup_right.trans (le_sup_left.trans hPS)
  have h₃S : R₃ ≤ (S₀ : Subgroup G) := le_sup_right.trans hPS
  have hzne : z ≠ t := hax.ne
  have h12 : R₁ ≠ R₂ := by
    intro h
    have htK : t ∈ K := hax.syl₁.1 (h ▸ hax.z_mem₂)
    rcases hstd.hz.unique t htK hstd.ht.sq with h1 | h1
    · exact hstd.ht.ne_one h1
    · exact hzne h1.symm
  have h13 : R₁ ≠ R₃ := by
    intro h
    have hK : z * t ∈ K := hax.syl₁.1 (h ▸ hax.z_mem₃)
    rcases hstd.hz.unique (z * t) hK hu.sq with h1 | h1
    · exact hu.ne_one h1
    · exact hstd.ht.ne_one (mul_left_cancel (h1.trans (mul_one z).symm))
  have h23 : R₂ ≠ R₃ := by
    intro h
    have hJ : z * t ∈ J := hax.syl₂.1 (h ▸ hax.z_mem₃)
    rcases hstd.ht.unique (z * t) hJ hu.sq with h1 | h1
    · exact hu.ne_one h1
    · exact hstd.hz.ne_one (mul_right_cancel (h1.trans (one_mul t).symm))
  have hRΩ : ∀ Q ∈ ({R₁, R₂, R₃} : Set (Subgroup G)), Q ∈ RSet Ω := by
    intro Q hQ
    rcases hQ with h | h | h <;> rw [h]
    · exact mem_RSet_of_isSylow2In hstd.stand.mem hax.syl₁
    · exact mem_RSet_of_isSylow2In hstd.hJ.1 hax.syl₂
    · exact mem_RSet_of_isSylow2In hset.nbrK.1 hax.syl₃
  have hQS : ∀ Q ∈ ({R₁, R₂, R₃} : Set (Subgroup G)), Q ≤ (S₀ : Subgroup G) := by
    intro Q hQ
    rcases hQ with h | h | h <;> rw [h]
    exacts [h₁S, h₂S, h₃S]
  have hstab : ∀ s ∈ (S₀ : Subgroup G), ∀ Q ∈ ({R₁, R₂, R₃} : Set (Subgroup G)),
      conjSub s Q ∈ ({R₁, R₂, R₃} : Set (Subgroup G)) := by
    intro s hs Q hQ
    have h1 : conjSub s Q ∈ RSet Ω := RSet.conj hΩ.conjInvariant (hRΩ Q hQ) s
    have h2 : conjSub s Q ≤ (S₀ : Subgroup G) :=
      (conjSub_mono (hQS Q hQ)).trans (conjSub_eq_self_of_mem hs).le
    rcases hset.eq_axis_of_mem_RSet_of_le hax h₁S h₂S h₃S h1 h2 with e | e | e
    exacts [Or.inl e, Or.inr (Or.inl e), Or.inr (Or.inr e)]
  obtain ⟨Q, hQV, hfix⟩ := exists_fixed_conj_of_three S₀.isPGroup' h12 h13 h23 hstab
  have key : ∃ g : G, ∀ s ∈ (S₀ : Subgroup G), s * (g * z * g⁻¹) * s⁻¹ = g * z * g⁻¹ := by
    rcases hQV with h | h | h <;> rw [h] at hfix
    · exact ⟨1, fun s hs => by
        simpa using mul_conj_eq_of_conjSub_eq hstd.hz hax.z_mem₁ hax.syl₁.1 (hfix s hs)⟩
    · obtain ⟨g, hg⟩ := hset.exists_conj_of_uniq hstd.hJ.1 hstd.ht
      exact ⟨g, fun s hs => by
        rw [← hg]
        exact mul_conj_eq_of_conjSub_eq hstd.ht hax.z_mem₂ hax.syl₂.1 (hfix s hs)⟩
    · obtain ⟨g, hg⟩ := hset.exists_conj_of_uniq hset.nbrK.1 hu
      exact ⟨g, fun s hs => by
        rw [← hg]
        exact mul_conj_eq_of_conjSub_eq hu hax.z_mem₃ hax.syl₃.1 (hfix s hs)⟩
  obtain ⟨g, hg⟩ := key
  have hS'syl : IsSylow2In (conjSub g⁻¹ (S₀ : Subgroup G)) ⊤ :=
    isSylow2In_top_conj (isSylow2In_top_of_sylow S₀) g⁻¹
  have hS'le : conjSub g⁻¹ (S₀ : Subgroup G) ≤ Subgroup.centralizer ({z} : Set G) := by
    intro x hx
    rw [mem_conjSub_iff, inv_inv] at hx
    have h1 := hg _ hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h2 : x * z * x⁻¹ = z := by
      calc x * z * x⁻¹ = g⁻¹ * ((g * x * g⁻¹) * (g * z * g⁻¹) * (g * x * g⁻¹)⁻¹) * g := by group
        _ = g⁻¹ * (g * z * g⁻¹) * g := by rw [h1]
        _ = z := by group
    calc x * z = x * z * x⁻¹ * x := by group
      _ = z * x := by rw [h2]
  have hE_le : Subgroup.closure ({z, t} : Set G) ≤ (S₀ : Subgroup G) :=
    (Subgroup.closure_le _).mpr (by
      rintro y (rfl | rfl)
      · exact h₁S hax.z_mem₁
      · exact h₂S hax.z_mem₂)
  have hE2 : IsPGroup 2 (Subgroup.closure ({z, t} : Set G)) := S₀.isPGroup'.to_le hE_le
  have hEC : Subgroup.closure ({z, t} : Set G) ≤ Subgroup.centralizer ({z} : Set G) :=
    (Subgroup.closure_le _).mpr (by
      rintro y (rfl | rfl)
      · exact Subgroup.mem_centralizer_singleton_iff.mpr rfl
      · exact Subgroup.mem_centralizer_singleton_iff.mpr hzt.symm)
  exact exists_isSylow2In_top_between hS'syl hS'le hE2 hEC

end Central

end CFSG.ClassicalInvolution.Q3.Q3AM
