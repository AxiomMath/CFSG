module

public import CFSG.Fischer.Uniq.Hyperoval
public import CFSG.Fischer.Uniq.CountFar
public import CFSG.Fischer.Uniq.LocalPoints

public section

namespace CFSG.Fischer

open CFSG.Blueprint.Fischer

variable {X : Type} [Group X] {E : Set X}

theorem F22.nonempty_localPoints
    (hF : F22 X E) {e : X} (he : e ∈ E) :
    Nonempty (LocalPoints polarModel E e) := by
  obtain ⟨χ, hcomm, htau⟩ := F22.exists_localPoints hF he
  exact ⟨⟨χ, hcomm, htau⟩⟩

section Polar

variable (hPF : PolarFacts) (hP : Pair X E) (hloc : ∀ f ∈ E, Nonempty (LocalPoints polarModel E f))
include hPF hP hloc

theorem LocalPoints.muImg_fib {d : X} (hd : d ∈ E) (L : LocalPoints polarModel E d) {c c' : X}
    (hc : c ∈ farSet E d) (hc' : c' ∈ farSet E d) (h : L.muImg c = L.muImg c') :
    c' = c ∨ c' = d * c * d := by
  have hmu : ∀ s, s ∈ muSet E d c ↔ s ∈ muSet E d c' := by
    intro s
    constructor
    · intro hs
      have := (L.χ_mem_muImg_iff ⟨s, hs.1⟩).2 hs
      rw [h] at this
      exact (L.χ_mem_muImg_iff ⟨s, hs.1⟩).1 this
    · intro hs
      have := (L.χ_mem_muImg_iff ⟨s, hs.1⟩).2 hs
      rw [← h] at this
      exact (L.χ_mem_muImg_iff ⟨s, hs.1⟩).1 this
  obtain ⟨f, hf⟩ := hc.2.2
  have hf' := (hmu f).1 hf
  have hdf : d ∈ LocalClass E f := ⟨hd, hf.1.2.1.symm, hf.1.2.2.symm⟩
  have hcf : c ∈ LocalClass E f := ⟨hc.1, hf.2.2.1.symm, hf.2.2.2.symm⟩
  have hc'f : c' ∈ LocalClass E f := ⟨hc'.1, hf'.2.2.1.symm, hf'.2.2.2.symm⟩
  obtain ⟨Lf⟩ := hloc f hf.1.1
  have hab : ¬ perp (Lf.χ ⟨d, hdf⟩) (Lf.χ ⟨c, hcf⟩) := fun e =>
    hc.2.1 ((Lf.comm ⟨d, hdf⟩ ⟨c, hcf⟩).2 e).symm
  have hab' : ¬ perp (Lf.χ ⟨d, hdf⟩) (Lf.χ ⟨c', hc'f⟩) := fun e =>
    hc'.2.1 ((Lf.comm ⟨d, hdf⟩ ⟨c', hc'f⟩).2 e).symm
  have hN : ∀ w, perp w (Lf.χ ⟨d, hdf⟩) ∧ perp w (Lf.χ ⟨c, hcf⟩) ↔
      perp w (Lf.χ ⟨d, hdf⟩) ∧ perp w (Lf.χ ⟨c', hc'f⟩) := by
    intro w
    have h1 := Lf.mem_muSet_iff_perp hdf hcf hc.2.1 (Lf.χ.symm w)
    have h2 := Lf.mem_muSet_iff_perp hdf hc'f hc'.2.1 (Lf.χ.symm w)
    rw [Equiv.apply_symm_apply] at h1 h2
    rw [← h1, ← h2]
    exact hmu _
  rcases hPF.eq_of_perp_perp _ _ _ hab hab' hN with e | e
  · left
    exact congrArg Subtype.val (Lf.χ.injective e)
  · right
    have hdcd : d * c * d ∈ LocalClass E f := by
      refine ⟨Pair.mul_mul_mem hP hd hc.1, fun e => ?_, ?_⟩
      · apply Pair.mul_mul_not_commute_left hP hd (fun e => hc.2.1 e.symm)
        rw [e]
        exact hf.1.2.2
      · have h1 : Commute d f := hdf.2.2
        have h2 : Commute c f := hcf.2.2
        exact ((h1.mul_left h2).mul_left h1 : Commute (d * c * d) f)
    have := Lf.tau ⟨d, hdf⟩ ⟨c, hcf⟩ hdcd
    rw [polarModel_tv, ← e] at this
    exact (congrArg Subtype.val (Lf.χ.injective this)).symm

theorem Pair.ncard_muSet_of_polar {d c : X} (hd : d ∈ E) (hc : c ∈ farSet E d) :
    (muSet E d c).ncard = 126 := by
  obtain ⟨L⟩ := hloc d hd
  have hO := Pair.isClosedHyperoval_muImg hPF hP hd hc.1 hc.2.1 L hloc
  have hne : (L.muImg c).Nonempty := (L.muImg_nonempty_iff c).2 hc.2.2
  obtain ⟨i, hi⟩ := hPF.exists_mem_hypOrbit _ hO hne
  rw [← L.ncard_muImg, hPF.ncard_of_mem_hypOrbit i _ hi]

omit hPF hP in
theorem ncard_localClass_of_polar {f : X} (hf : f ∈ E) : (LocalClass E f).ncard = 693 := by
  obtain ⟨L⟩ := hloc f hf
  rw [← Nat.card_coe_set_eq, Nat.card_congr L.χ, Nat.card_eq_fintype_card, Fintype.card_fin]

omit hP in
theorem ncard_localClass_inter_of_polar {d f : X} (hd : d ∈ E) (hf : f ∈ LocalClass E d) :
    (LocalClass E d ∩ LocalClass E f).ncard = 180 := by
  obtain ⟨L⟩ := hloc d hd
  rw [← hPF.ncard_perp_ne (L.χ ⟨f, hf⟩)]
  refine Set.ncard_congr (fun g hg => L.χ ⟨g, hg.1⟩) (fun g hg => ?_)
    (fun g g' hg hg' e => congrArg Subtype.val (L.χ.injective e)) (fun q hq => ?_)
  · refine ⟨(L.comm ⟨f, hf⟩ ⟨g, hg.1⟩).1 hg.2.2.2.symm, fun e => hg.2.2.1 ?_⟩
    exact congrArg Subtype.val (L.χ.injective e)
  · refine ⟨L.χ.symm q, ⟨(L.χ.symm q).2, (L.χ.symm q).2.1, fun e => hq.2 ?_, ?_⟩, ?_⟩
    · have : L.χ.symm q = ⟨f, hf⟩ := Subtype.ext e
      rw [← this, Equiv.apply_symm_apply]
    · have := (L.comm ⟨f, hf⟩ (L.χ.symm q)).2 (by rw [Equiv.apply_symm_apply]; exact hq.1)
      exact this.symm
    · exact Equiv.apply_symm_apply _ _

theorem Pair.ncard_farSet_of_polar {d : X} (hd : d ∈ E) : (farSet E d).ncard = 2816 := by
  have h := Pair.ncard_farSet hP hd (ncard_localClass_of_polar hloc hd)
    (fun f hf => ncard_localClass_of_polar hloc hf.1)
    (fun f hf => ncard_localClass_inter_of_polar hPF hloc hd hf)
    (fun c hc => Pair.ncard_muSet_of_polar hPF hP hloc hd hc)
  omega

omit hPF hloc in
theorem Pair.star_conj_mem_farSet {d : X} (f : LocalClass E d) {c : X}
    (hc : c ∈ farSet E d) : (f : X) * c * f ∈ farSet E d := by
  have hfE : (f : X) ∈ E := f.2.1
  have hff : (f : X) * f = 1 := Pair.mul_self hP hfE
  have hfd : (f : X) * d * f = d := by
    rw [f.2.2.2, mul_assoc, hff, mul_one]
  refine ⟨Pair.mul_mul_mem hP hfE hc.1, fun h => hc.2.1 ?_, ?_⟩
  · calc c * d = f * (f * c * f * d) * f := by
          rw [show (f : X) * (f * c * f * d) * f = (f * f) * c * (f * d * f) by group, hff, hfd,
            one_mul]
      _ = f * (d * (f * c * f)) * f := by rw [h]
      _ = d * c := by
          rw [show (f : X) * (d * (f * c * f)) * f = (f * d * f) * c * (f * f) by group, hfd, hff,
            mul_one]
  · obtain ⟨s, hs⟩ := hc.2.2
    have h := Pair.image_conj_muSet hP f d c
    rw [Pair.inv_eq hP hfE, hfd] at h
    rw [← h]
    exact ⟨_, s, hs, rfl⟩

theorem LocalPoints.exists_family_eq_hypOrbit {d : X} (hd : d ∈ E)
    (L : LocalPoints polarModel E d) : ∃ i, L.muImg '' farSet E d = hypOrbit i := by
  have := Pair.finite hP
  set 𝒮 := L.muImg '' farSet E d with h𝒮
  have hinv : ∀ O ∈ 𝒮, ∀ p, tvP p '' O ∈ 𝒮 := by
    rintro O ⟨c, hc, rfl⟩ p
    refine ⟨_, Pair.star_conj_mem_farSet hP (L.χ.symm p) hc, ?_⟩
    rw [L.muImg_star_conj hP, Equiv.apply_symm_apply]
    rfl
  have hcard := Pair.ncard_farSet_of_polar hPF hP hloc hd
  obtain ⟨c₀, hc₀⟩ := Set.nonempty_of_ncard_ne_zero (s := farSet E d) (by rw [hcard]; norm_num)
  have hO₀ := Pair.isClosedHyperoval_muImg hPF hP hd hc₀.1 hc₀.2.1 L hloc
  obtain ⟨i, hi⟩ := hPF.exists_mem_hypOrbit _ hO₀ ((L.muImg_nonempty_iff c₀).2 hc₀.2.2)
  refine ⟨i, (Set.eq_of_subset_of_ncard_le
    (hPF.hypOrbit_subset_of_invariant 𝒮 hinv i _ ⟨c₀, hc₀, rfl⟩ hi) ?_ (Set.toFinite _)).symm⟩
  have h2 := ncard_mul_eq_ncard_mul (fun c O => L.muImg c = O) (s := farSet E d) (t := 𝒮)
    (m := 1) (n := 2) (fun c hc => ?_) (fun O hO => ?_)
  · rw [hcard] at h2
    rw [hPF.ncard_hypOrbit i]
    omega
  · have : {O | O ∈ 𝒮 ∧ L.muImg c = O} = {L.muImg c} := by
      ext O
      constructor
      · rintro ⟨-, rfl⟩; rfl
      · rintro rfl; exact ⟨⟨c, hc, rfl⟩, rfl⟩
    rw [this, Set.ncard_singleton]
  · obtain ⟨c₁, hc₁, rfl⟩ := hO
    have : {c | c ∈ farSet E d ∧ L.muImg c = L.muImg c₁} = {c₁, d * c₁ * d} := by
      ext c
      constructor
      · rintro ⟨hc, h⟩
        exact L.muImg_fib hPF hP hloc hd hc₁ hc h.symm
      · rintro (rfl | rfl)
        · exact ⟨hc₁, rfl⟩
        · exact ⟨conj_mem_farSet hP hd hc₁, L.muImg_conj hP hd hc₁.1 hc₁.2.1⟩
    rw [this, Set.ncard_pair (Pair.mul_mul_ne_right hP hd (fun e => hc₁.2.1 e.symm)).symm]

omit hP hloc in
theorem LocalPoints.family_relabel_delta {d : X} (L : LocalPoints polarModel E d) :
    (L.relabel delta hPF.perp_delta hPF.delta_tvP).muImg '' farSet E d =
      (fun O => ⇑delta '' O) '' (L.muImg '' farSet E d) := by
  rw [Set.image_image]
  exact Set.image_congr fun c _ => L.muImg_relabel _ _ _ c

theorem exists_localPoints_hypOrbit_zero {d : X} (hd : d ∈ E) :
    ∃ L : LocalPoints polarModel E d, L.muImg '' farSet E d = hypOrbit 0 := by
  obtain ⟨L⟩ := hloc d hd
  obtain ⟨i, hi⟩ := L.exists_family_eq_hypOrbit hPF hP hloc hd
  set L₁ := L.relabel delta hPF.perp_delta hPF.delta_tvP
  have h₁ : L₁.muImg '' farSet E d = hypOrbit (i + 1) := by
    rw [L.family_relabel_delta hPF, hi, hPF.image_delta_hypOrbit]
  set L₂ := L₁.relabel delta hPF.perp_delta hPF.delta_tvP
  have h₂ : L₂.muImg '' farSet E d = hypOrbit (i + 1 + 1) := by
    rw [L₁.family_relabel_delta hPF, h₁, hPF.image_delta_hypOrbit]
  fin_cases i
  · exact ⟨L, hi⟩
  · exact ⟨L₂, h₂⟩
  · exact ⟨L₁, h₁⟩

theorem coverHyp_hypOrbit_zero {d : X} (hd : d ∈ E) (L : LocalPoints polarModel E d)
    (hL : L.muImg '' farSet E d = hypOrbit 0) : CoverHyp L (hypOrbit 0) where
  mem c hc := hL ▸ ⟨c, hc, rfl⟩
  surj O hO := by
    rw [← hL] at hO
    obtain ⟨c, hc, rfl⟩ := hO
    exact ⟨c, hc, rfl⟩
  inj O hO := hPF.injOn_tvP_image O hO
  ne O hO f hf := hPF.tvP_image_ne O hO f hf
  fib _ hc _ hc' h := L.muImg_fib hPF hP hloc hd hc hc' h

end Polar

end CFSG.Fischer
