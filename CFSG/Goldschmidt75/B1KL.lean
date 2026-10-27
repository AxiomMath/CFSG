module

public import CFSG.Goldschmidt75.B1Comp2
public import CFSG.Goldschmidt75.Sec41a

public section

namespace CFSG.Goldschmidt75

open CFSG.Open CFSG.Goldschmidt Subgroup

variable {G : Type} [Group G] [Finite G]

theorem le_centralizer_normalClosure
    (T : Sylow 2 G) {A : Subgroup G} (hAT : A ≤ T)
    (hAab : IsMulCommutative A) (hA : fusionStronglyClosed (A : Set G) T)
    (hO : goldschmidtOddCore G = ⊥) {X : Subgroup G} (hX : ⁅X, X⁆ = X)
    (hXA : X ≤ centralizer (A : Set G)) :
    X ≤ centralizer (normalClosure (A : Set G) : Set G) := by
  set M := normalClosure (A : Set G) with hM
  have : M.Normal := normalClosure_normal
  have hAM : A ≤ M := le_normalClosure
  obtain ⟨TH, hTH, -, hcl, -⟩ := exists_sylow_subgroupOf T hAT hAT hA hA (sup_le hAM hAM)
  have hcore : CoreHyp M TH (A.subgroupOf M) :=
    ⟨hTH, isMulCommutative_subgroupOf hAab M, hcl, normalClosure_subgroupOf_eq_top T hAT hA rfl,
      oddCore_eq_bot_of_normal hO⟩
  have : Group.IsPerfect X := Subgroup.isPerfect_iff.mpr hX
  let Φ : X →* MulAut M := MulAut.conjNormal.comp X.subtype
  have hfix : ∀ g : X, ∀ a ∈ A.subgroupOf M, Φ g a = a := by
    intro g a ha
    apply Subtype.ext
    rw [mem_subgroupOf] at ha
    have hc := mem_centralizer_iff.mp (hXA g.2) a ha
    change (g : G) * a * (g : G)⁻¹ = a
    rw [← hc]
    group
  intro g hg
  have h1 := fix_of_coreHyp TH hcore Φ hfix ⟨g, hg⟩
  rw [mem_centralizer_iff]
  intro m hm
  have h2 := congrArg (fun β : MulAut M => ((β ⟨m, hm⟩ : M) : G)) h1
  change g * m * g⁻¹ = m at h2
  calc m * g = g * m * g⁻¹ * g := by rw [h2]
    _ = g * m := by group

omit [Finite G] in
theorem normalClosure_le_of_le_centralizer (T : Sylow 2 G) {A : Subgroup G} (hAT : A ≤ T)
    (hA : fusionStronglyClosed (A : Set G) T)
    (hAC : A ≤ centralizer (normalClosure (A : Set G) : Set G)) :
    normalClosure (A : Set G) ≤ A := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M := normalClosure (A : Set G) with hM
  have : M.Normal := normalClosure_normal
  have hMC : M ≤ centralizer (M : Set G) := normalClosure_le_normal fun a ha => hAC ha
  have h2 : ∀ m ∈ M, ∃ k : ℕ, m ^ (2 ^ k) = 1 := by
    intro m hm
    change m ∈ closure (Group.conjugatesOfSet (A : Set G)) at hm
    induction hm using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨a, ha, hax⟩ := Group.mem_conjugatesOfSet_iff.mp hx
      obtain ⟨c, rfl⟩ := isConj_iff.mp hax
      obtain ⟨k, hk⟩ := T.isPGroup' ⟨a, hAT ha⟩
      refine ⟨k, ?_⟩
      have hk' : a ^ (2 ^ k) = 1 := congrArg Subtype.val hk
      rw [conj_pow, hk']
      group
    | one => exact ⟨0, by simp⟩
    | mul x y hx hy ihx ihy =>
      obtain ⟨k₁, hk₁⟩ := ihx
      obtain ⟨k₂, hk₂⟩ := ihy
      have hxy : Commute x y := (mem_centralizer_iff.mp (hMC hy) x hx)
      refine ⟨k₁ + k₂, ?_⟩
      rw [hxy.mul_pow, pow_add, pow_mul, hk₁, one_pow, mul_comm (2 ^ k₁), pow_mul, hk₂, one_pow,
        one_mul]
    | inv x hx ih =>
      obtain ⟨k, hk⟩ := ih
      exact ⟨k, by rw [inv_pow, hk, inv_one]⟩
  have hp : IsPGroup 2 M := fun m => by
    obtain ⟨k, hk⟩ := h2 m m.2
    exact ⟨k, Subtype.ext (by simpa using hk)⟩
  have hMT : M ≤ T := hp.le_sylow_of_normal T
  refine (closure_le _).mpr ?_
  intro x hx
  obtain ⟨a, ha, hax⟩ := Group.mem_conjugatesOfSet_iff.mp hx
  obtain ⟨c, rfl⟩ := isConj_iff.mp hax
  have hxM : c * a * c⁻¹ ∈ M := conjugatesOfSet_subset_normalClosure hx
  have h := hA a ha c⁻¹ (by simpa using hMT hxM)
  simpa using h

end CFSG.Goldschmidt75
