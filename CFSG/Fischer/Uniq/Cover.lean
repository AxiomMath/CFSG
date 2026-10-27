module

public import CFSG.Fischer.Uniq.Model
public import CFSG.Fischer.Uniq.TwoCover

public section

namespace CFSG.Fischer

open CFSG.Blueprint.Fischer

variable {X : Type} [Group X] {E : Set X} {P : Type} {M : LocalModel P}

@[expose] def farSet (E : Set X) (d : X) : Set X :=
  {c | c ∈ E ∧ c * d ≠ d * c ∧ (muSet E d c).Nonempty}

theorem mem_farSet {d c : X} :
    c ∈ farSet E d ↔ c ∈ E ∧ c * d ≠ d * c ∧ (muSet E d c).Nonempty :=
  Iff.rfl

structure CoverHyp {d : X} (L : LocalPoints M E d) (𝒮 : Set (Set P)) : Prop where
  mem : ∀ c ∈ farSet E d, L.muImg c ∈ 𝒮
  surj : ∀ O ∈ 𝒮, ∃ c ∈ farSet E d, L.muImg c = O
  inj : ∀ O ∈ 𝒮, Set.InjOn (fun f => M.tv f '' O) Oᶜ
  ne : ∀ O ∈ 𝒮, ∀ f ∉ O, M.tv f '' O ≠ O
  fib : ∀ c ∈ farSet E d, ∀ c' ∈ farSet E d, L.muImg c = L.muImg c' → c' = c ∨ c' = d * c * d

@[expose] def farGraph (E : Set X) (d : X) : SimpleGraph (farSet E d) where
  Adj c c' := (c : X) ≠ c' ∧ (c : X) * c' = c' * c
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

theorem farGraph_adj {d : X} {c c' : farSet E d} :
    (farGraph E d).Adj c c' ↔ (c : X) ≠ c' ∧ (c : X) * c' = c' * c :=
  Iff.rfl

section Cover

variable {d : X} (hP : Pair X E) (hd : d ∈ E) (L : LocalPoints M E d) {𝒮 : Set (Set P)}
  (h : CoverHyp L 𝒮)
include hP hd

theorem nu_mem_farSet {c : X} (hc : c ∈ farSet E d) (f : LocalClass E d)
    (hf : (f : X) ∉ muSet E d c) : d * c * f * c * d ∈ farSet E d := by
  refine ⟨(Pair.nu_mem_localClass hP hd hc.1 hc.2.1 f.2).1,
    Pair.nu_not_commute hP hd hc.1 hc.2.1 f.2 hf, ?_⟩
  rw [Pair.muSet_nu hP hd hc.1 hc.2.1 f.2 hf]
  exact hc.2.2.image _

theorem conj_mem_farSet {c : X} (hc : c ∈ farSet E d) : d * c * d ∈ farSet E d := by
  refine ⟨Pair.mul_mul_mem hP hd hc.1, Pair.mul_mul_not_commute_left hP hd
    (fun e => hc.2.1 e.symm), ?_⟩
  rw [← Pair.muSet_eq_muSet_mul_mul hP hd hc.1 hc.2.1]
  exact hc.2.2

theorem adj_nu {c c' : farSet E d} (hadj : (farGraph E d).Adj c c') :
    ∃ f : LocalClass E d, (f : X) ∉ muSet E d c ∧ (c' : X) = d * c * f * c * d := by
  have hc' : (c' : X) ∈ LocalClass E c := ⟨c'.2.1, hadj.1.symm, hadj.2.symm⟩
  obtain ⟨f, hf, hfc, hfe⟩ := Pair.exists_nu hP hd c.2.1 c.2.2.1 hc' c'.2.2.1
  exact ⟨⟨f, hf⟩, hfc, hfe.symm⟩

include h

@[expose] noncomputable def coverOf : TwoCover (M.xi 𝒮) (fun O Q R => M.triRule O Q R) where
  C := farSet E d
  π c := ⟨L.muImg c, h.mem c c.2⟩
  adj := farGraph E d
  proj := by
    intro c c' hadj
    obtain ⟨f, hfc, hfe⟩ := adj_nu hP hd hadj
    have hQ : L.muImg (c' : X) = M.tv (L.χ f) '' L.muImg c := by
      rw [hfe, L.muImg_nu hP hd c.2.1 c.2.2.1 f hfc]
    refine ⟨fun heq => ?_, L.χ f, (L.χ_mem_muImg_iff f).not.2 hfc, hQ.symm⟩
    have := congrArg Subtype.val heq
    simp only at this
    exact h.ne _ (h.mem c c.2) (L.χ f) ((L.χ_mem_muImg_iff f).not.2 hfc)
      (hQ.symm.trans this.symm)
  lift := by
    intro c Q hQ
    obtain ⟨-, g, hg, hgQ⟩ := hQ
    set f := L.χ.symm g
    have hfg : L.χ f = g := Equiv.apply_symm_apply _ _
    have hfc : (f : X) ∉ muSet E d c := by
      rw [← L.χ_mem_muImg_iff, hfg]; exact hg
    refine ⟨⟨_, nu_mem_farSet hP hd c.2 f hfc⟩, ⟨?_, ?_⟩, ?_⟩
    · have hl := Pair.nu_mem_localClass hP hd c.2.1 c.2.2.1 f.2
      exact ⟨hl.2.1.symm, hl.2.2.symm⟩
    · apply Subtype.ext
      show L.muImg (d * c * f * c * d) = Q
      rw [L.muImg_nu hP hd c.2.1 c.2.2.1 f hfc, hfg, hgQ]
    · rintro c'' ⟨hadj, hπ⟩
      obtain ⟨f'', hf''c, hf''e⟩ := adj_nu hP hd hadj
      have h1 : M.tv (L.χ f'') '' L.muImg c = M.tv g '' L.muImg c := by
        have := congrArg Subtype.val hπ
        simp only at this
        rw [hgQ, ← this, hf''e, L.muImg_nu hP hd c.2.1 c.2.2.1 f'' hf''c]
      have h2 := h.inj _ (h.mem c c.2) ((L.χ_mem_muImg_iff f'').not.2 hf''c) hg h1
      have h3 : f'' = f := by rw [← hfg] at h2; exact L.χ.injective h2
      apply Subtype.ext
      rw [hf''e, h3]
  two := by
    rintro ⟨O, hO⟩
    obtain ⟨c, hc, hcO⟩ := h.surj O hO
    refine ⟨⟨c, hc⟩, ⟨d * c * d, conj_mem_farSet hP hd hc⟩, fun e => ?_, ?_, ?_, ?_⟩
    · have := congrArg Subtype.val e
      exact Pair.mul_mul_ne_right hP hd (fun e => hc.2.1 e.symm) this.symm
    · exact Subtype.ext hcO
    · apply Subtype.ext
      show L.muImg (d * c * d) = O
      rw [L.muImg_conj hP hd hc.1 hc.2.1, hcO]
    · rintro x hx
      have hx' : L.muImg c = L.muImg (x : X) := by
        rw [hcO]; exact (congrArg Subtype.val hx).symm
      rcases h.fib c hc x x.2 hx' with e | e
      · left; exact Subtype.ext e
      · right; exact Subtype.ext e
  tri := by
    intro c c₁ c₂ h₁ h₂ h₁₂
    obtain ⟨f₁, hf₁, he₁⟩ := adj_nu hP hd h₁
    obtain ⟨f₂, hf₂, he₂⟩ := adj_nu hP hd h₂
    have hQ₁ : L.muImg (c₁ : X) = M.tv (L.χ f₁) '' L.muImg c := by
      rw [he₁, L.muImg_nu hP hd c.2.1 c.2.2.1 f₁ hf₁]
    have hQ₂ : L.muImg (c₂ : X) = M.tv (L.χ f₂) '' L.muImg c := by
      rw [he₂, L.muImg_nu hP hd c.2.1 c.2.2.1 f₂ hf₂]
    have hne : (c₁ : X) ≠ c₂ := by
      intro e
      apply h₁₂.1
      apply Subtype.ext
      show L.muImg (c₁ : X) = L.muImg (c₂ : X)
      rw [e]
    show (farGraph E d).Adj c₁ c₂ ↔ M.triRule (L.muImg c) (L.muImg c₁) (L.muImg c₂)
    have hcomm : (c₁ : X) * c₂ = c₂ * c₁ ↔ M.perp (L.χ f₁) (L.χ f₂) := by
      rw [he₁, he₂, Pair.nu_commute_iff hP hd c.2.1]
      exact L.comm f₁ f₂
    constructor
    · rintro ⟨-, hc⟩
      exact ⟨L.χ f₁, L.χ f₂, (L.χ_mem_muImg_iff f₁).not.2 hf₁, (L.χ_mem_muImg_iff f₂).not.2 hf₂,
        hQ₁.symm, hQ₂.symm, hcomm.1 hc⟩
    · rintro ⟨f, g, hf, hg, hfQ, hgR, hperp⟩
      have e1 := h.inj _ (h.mem c c.2) hf ((L.χ_mem_muImg_iff f₁).not.2 hf₁)
        (hfQ.trans hQ₁)
      have e2 := h.inj _ (h.mem c c.2) hg ((L.χ_mem_muImg_iff f₂).not.2 hf₂)
        (hgR.trans hQ₂)
      exact ⟨hne, hcomm.2 (by rw [← e1, ← e2]; exact hperp)⟩

theorem coverOf_C : (coverOf hP hd L h).C = farSet E d := rfl

theorem coverOf_π (c : farSet E d) :
    ((coverOf hP hd L h).π c : Set P) = L.muImg (c : X) := rfl

theorem coverOf_adj (c c' : farSet E d) :
    (coverOf hP hd L h).adj.Adj c c' ↔ (farGraph E d).Adj c c' := Iff.rfl

end Cover

end CFSG.Fischer
