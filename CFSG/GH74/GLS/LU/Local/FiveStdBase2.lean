module

public import CFSG.GH74.GLS.LU.Local.FiveStdBase

public section

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.GH74.GLS CFSG.GH74.GLS.LU.Local

open scoped Pointwise

namespace CFSG.GH74.GLS.LU.Local.Five

open CFSG.GH74.GLS.LU.Local.FiveStd

namespace FiveStdSetting

open FiveStdBase

variable {G : Type} [Group G] [Finite G] (st : FiveStdSetting G)

omit [Finite G] in
theorem S0_facts (hb : baseCheck = true) :
    ∃ S0G : Subgroup G, (S0G : Set G) = S st.ι S0 ∧ Nat.card ↥S0G = 128 ∧ IsPGroup 2 ↥S0G ∧
      st.z ∈ S0G ∧ (∀ s ∈ S0G, s * st.z = st.z * s) ∧
      (∀ g ∈ S0G, (∀ s ∈ S0G, s * g = g * s) → g = 1 ∨ g = st.z) ∧
      Nat.card ↥(Cz st.z) = 28800 ∧
      ∀ c ∈ Cz st.z, ∃ k ∈ st.K₁ ⊔ st.K₂, ∃ s ∈ S0G, c = k * s := by
  obtain ⟨-, -, -, hVS0, -, hnd, hlen, h1S, hzS, hzc, hmul, hinv, hcen, -, hcov⟩ := baseCheck_spec hb
  obtain ⟨S0G, hS⟩ := st.model.exists_sub hVS0 h1S hmul hinv
  have hmemS : ∀ g, g ∈ S0G ↔ ∃ x ∈ S0, st.ι x = g := fun g => by
    rw [← SetLike.mem_coe, hS]
    exact mem_S
  have hcard : Nat.card ↥S0G = 128 := by
    rw [natCard_eq_of_coe S0G hS, natCard_S st.model hVS0 hnd, hlen]
  have hzv : validE zE = true := hVS0 _ hzS
  have h1v : validE oneE = true := st.model.valid_one
  refine ⟨S0G, hS, hcard, IsPGroup.of_card (n := 7) (by rw [hcard]; norm_num), (hmemS _).2 ⟨zE, hzS, rfl⟩, ?_, ?_,
    st.card_Cz hb, ?_⟩
  · intro s hs
    obtain ⟨y, hy, rfl⟩ := (hmemS s).1 hs
    exact ((st.model.commE_iff hzv (hVS0 y hy)).1 (hzc y hy)).symm
  · intro g hg hgc
    obtain ⟨x, hx, rfl⟩ := (hmemS g).1 hg
    have hmemF : ∀ w, w ∈ S0.filter (fun x => S0.all fun y => commE x y) ↔
        w ∈ S0 ∧ ∀ y ∈ S0, commE w y = true := fun w => by
      rw [List.mem_filter, List.all_eq_true]
    have hxF : x ∈ S0.filter (fun x => S0.all fun y => commE x y) := by
      rw [hmemF]
      refine ⟨hx, fun y hy => ?_⟩
      exact (st.model.commE_iff (hVS0 x hx) (hVS0 y hy)).2 (hgc (st.ι y) ((hmemS _).2 ⟨y, hy, rfl⟩)).symm
    have h1F : oneE ∈ S0.filter (fun x => S0.all fun y => commE x y) := by
      rw [hmemF]
      refine ⟨h1S, fun y hy => ?_⟩
      rw [st.model.commE_iff h1v (hVS0 y hy), st.model.map_one]
      simp
    have hzF : zE ∈ S0.filter (fun x => S0.all fun y => commE x y) := (hmemF _).2 ⟨hzS, hzc⟩
    have hne : oneE ≠ zE := fun h => by
      have := congrArg (fun e => e.b0.val) h
      simp [oneE, zE] at this
    obtain ⟨a, b, hab⟩ := List.length_eq_two.1 hcen
    rw [hab] at hxF h1F hzF
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hxF h1F hzF
    have hx2 : x = oneE ∨ x = zE := by
      rcases hxF with rfl | rfl <;> rcases h1F with h | h <;> rcases hzF with h' | h' <;>
        first | exact absurd (h.trans h'.symm) hne | exact Or.inl h.symm | exact Or.inr h'.symm
    rcases hx2 with rfl | rfl
    · exact Or.inl st.model.map_one
    · exact Or.inr rfl
  · intro c hc
    obtain ⟨cE, hcv, rfl⟩ := st.mem_C_iff.1 hc
    obtain ⟨sE, hsE, hk⟩ := hcov cE ((mem_Cs_iff cE).2 hcv)
    have hsv : validE sE = true := hVS0 sE hsE
    have hkv : validE (mulE cE (invE sE)) = true := st.model.valid_mul _ _ hcv (st.model.valid_inv _ hsv)
    obtain ⟨a, ha, b, hb', hab⟩ := Set.mem_mul.1 ((st.hKK _ hkv).1 hk)
    refine ⟨st.ι (mulE cE (invE sE)), ?_, st.ι sE, (hmemS _).2 ⟨sE, hsE, rfl⟩, ?_⟩
    · rw [← hab]
      exact Subgroup.mul_mem_sup ha hb'
    · rw [st.model.map_mul _ _ hcv (st.model.valid_inv _ hsv), st.model.map_inv _ hsv]
      simp

end FiveStdSetting

end CFSG.GH74.GLS.LU.Local.Five
