module

public import CFSG.Fischer.Uniq.F23Hyperoval

public section

namespace CFSG.Fischer

open CFSG.Blueprint.Fischer

variable {X Y : Type} [Group X] [Group Y] {E : Set X} {F : Set Y}

theorem LocalPoints.muSet_eq_of_muImg_eq {P : Type} {M : LocalModel P} {d : X}
    (L : LocalPoints M E d) {c c' : X} (h : L.muImg c = L.muImg c') :
    muSet E d c = muSet E d c' := by
  ext s
  constructor
  · intro hs
    have := (L.χ_mem_muImg_iff ⟨s, hs.1⟩).2 hs
    rw [h] at this
    exact (L.χ_mem_muImg_iff ⟨s, hs.1⟩).1 this
  · intro hs
    have := (L.χ_mem_muImg_iff ⟨s, hs.1⟩).2 hs
    rw [← h] at this
    exact (L.χ_mem_muImg_iff ⟨s, hs.1⟩).1 this

theorem F22.muSet_fib
    (hPF : PolarFacts) (hF : F22 Y F) (hconnF : (commGraph F).Connected)
    {p q q' : Y} (hp : p ∈ F) (hq : q ∈ F) (hq' : q' ∈ F) (hpq : q * p ≠ p * q)
    (hpq' : q' * p ≠ p * q') (h : muSet F p q = muSet F p q') : q' = q ∨ q' = p * q * p := by
  have hloc : ∀ f ∈ F, Nonempty (LocalPoints polarModel F f) :=
    fun f hf => F22.nonempty_localPoints hF hf
  obtain ⟨L⟩ := hloc p hp
  have hqf : q ∈ farSet F p := ⟨hq, hpq, Pair.muSet_nonempty hF.1 hconnF hp hq hpq⟩
  have hqf' : q' ∈ farSet F p := ⟨hq', hpq', Pair.muSet_nonempty hF.1 hconnF hp hq' hpq'⟩
  refine L.muImg_fib hPF hF.1 hloc hp hqf hqf' ?_
  ext r
  rw [← Equiv.apply_symm_apply L.χ r, L.χ_mem_muImg_iff, L.χ_mem_muImg_iff, h]

section Model

variable (hPF : PolarFacts) (hF : F22 Y F) (hconnF : (commGraph F).Connected) (hE : Pair X E)
  (hloc : ∀ f ∈ E, Nonempty (LocalPoints (pairModel hF.1) E f))
include hPF hF hconnF hE hloc

theorem LocalPoints.muImg_fib_of_model {d : X} (hd : d ∈ E) (L : LocalPoints (pairModel hF.1) E d)
    {c c' : X} (hc : c ∈ farSet E d) (hc' : c' ∈ farSet E d) (h : L.muImg c = L.muImg c') :
    c' = c ∨ c' = d * c * d := by
  have hmu := L.muSet_eq_of_muImg_eq h
  obtain ⟨f, hf⟩ := hc.2.2
  have hf' : f ∈ muSet E d c' := hmu ▸ hf
  have hdf : d ∈ LocalClass E f := ⟨hd, hf.1.2.1.symm, hf.1.2.2.symm⟩
  have hcf : c ∈ LocalClass E f := ⟨hc.1, hf.2.2.1.symm, hf.2.2.2.symm⟩
  have hc'f : c' ∈ LocalClass E f := ⟨hc'.1, hf'.2.2.1.symm, hf'.2.2.2.symm⟩
  obtain ⟨Lf⟩ := hloc f hf.1.1
  set p := Lf.χ ⟨d, hdf⟩
  set q := Lf.χ ⟨c, hcf⟩
  set q' := Lf.χ ⟨c', hc'f⟩
  have hpq : (q : Y) * p ≠ p * q := fun e => hc.2.1 ((Lf.comm ⟨c, hcf⟩ ⟨d, hdf⟩).2 e)
  have hpq' : (q' : Y) * p ≠ p * q' := fun e => hc'.2.1 ((Lf.comm ⟨c', hc'f⟩ ⟨d, hdf⟩).2 e)
  have key : ∀ c₀ (hc₀ : c₀ ∈ LocalClass E f), ∀ g : LocalClass E f,
      ((Lf.χ g : F) : Y) ∈ muSet F (p : Y) (Lf.χ ⟨c₀, hc₀⟩ : Y) ↔
        (g : X) ∈ muSet E d c₀ := by
    intro c₀ hc₀ g
    rw [muSet, Set.mem_inter_iff, ← Lf.mem_localClass_iff hF.1 ⟨d, hdf⟩ g,
      ← Lf.mem_localClass_iff hF.1 ⟨c₀, hc₀⟩ g]
    rfl
  have hmuF : muSet F (p : Y) (q : Y) = muSet F (p : Y) (q' : Y) := by
    ext y
    constructor
    · intro hy
      obtain ⟨g, hg⟩ := Lf.χ.surjective ⟨y, hy.1.1⟩
      have hy' : ((Lf.χ g : F) : Y) ∈ muSet F (p : Y) (q : Y) := by rw [hg]; exact hy
      rw [key c hcf g, hmu, ← key c' hc'f g, hg] at hy'
      exact hy'
    · intro hy
      obtain ⟨g, hg⟩ := Lf.χ.surjective ⟨y, hy.1.1⟩
      have hy' : ((Lf.χ g : F) : Y) ∈ muSet F (p : Y) (q' : Y) := by rw [hg]; exact hy
      rw [key c' hc'f g, ← hmu, ← key c hcf g, hg] at hy'
      exact hy'
  rcases F22.muSet_fib hPF hF hconnF p.2 q.2 q'.2 hpq hpq' hmuF with e | e
  · left
    exact congrArg Subtype.val (Lf.χ.injective (Subtype.ext e))
  · right
    have hdcd : d * c * d ∈ LocalClass E f :=
      LocalPoints.mul_mul_mem_localClass hE (⟨d, hdf⟩ : LocalClass E f) ⟨c, hcf⟩
    have h1 := congrArg Subtype.val (Lf.tau ⟨d, hdf⟩ ⟨c, hcf⟩ hdcd)
    rw [pairModel_tv] at h1
    rw [← e] at h1
    exact (congrArg Subtype.val (Lf.χ.injective (Subtype.ext h1))).symm

omit hPF hconnF hE in
theorem ncard_localClass_of_model {f : X} (hf : f ∈ E) : (LocalClass E f).ncard = F.ncard := by
  obtain ⟨L⟩ := hloc f hf
  rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq, Nat.card_congr L.χ]

omit hPF hconnF hE in
theorem ncard_localClass_inter_of_model {d f : X} (hd : d ∈ E) (hf : f ∈ LocalClass E d) :
    ∃ p ∈ F, (LocalClass E d ∩ LocalClass E f).ncard = (LocalClass F p).ncard := by
  obtain ⟨L⟩ := hloc d hd
  refine ⟨_, (L.χ ⟨f, hf⟩).2, ?_⟩
  rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq, Nat.card_congr (L.restrictStar hF.1 ⟨f, hf⟩)]

end Model

end CFSG.Fischer
