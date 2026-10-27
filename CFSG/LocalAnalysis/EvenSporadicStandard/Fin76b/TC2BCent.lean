module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.Lemma65Comm

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup
open scoped Pointwise

variable {G : Type*} [Group G] [Finite G] {L : Subgroup G} {z t : G} {E : Subgroup G}

theorem B_centralizes_S_gen (hW : WFacts L t E) (hzL : ∀ a ∈ L, a * z = z * a)
    (htz : t * z = z * t) {B : Subgroup G} (hBL : B ≤ L) (hBt : B ≤ centralizer ({t} : Set G))
    (hB : Nonempty (↥B ≃* alternatingGroup (Fin 5))) {S : Subgroup G} (hS2 : IsPGroup 2 S)
    (hSC : S ≤ centralizer (E : Set G))
    (hSmax : ∀ R : Subgroup G, IsPGroup 2 R → R ≤ centralizer (E : Set G) → S ≤ R → R = S)
    (hzS : z ∈ S) [Group.IsSolvable (MulAut ↥S)]
    (hV : ∀ v ∈ centralizer (E : Set G), v * z = z * v → v = 1 ∨ v = z ∨ v = t ∨ v = t * z) :
    ∀ b ∈ B, ∀ s ∈ S, b * s = s * b := by
  classical
  set M : Subgroup G := centralizer (E : Set G) with hMdef
  have hBE : ∀ b ∈ B, ∀ e ∈ E, b * e * b⁻¹ ∈ E := fun b hb e he =>
    hW.normal b (hBL hb) (mem_centralizer_singleton_iff.1 (hBt hb)) e he
  have hBM : ∀ b ∈ B, ∀ m ∈ M, b * m * b⁻¹ ∈ M := by
    intro b hb m hm
    rw [hMdef, mem_centralizer_iff]
    intro e he
    have h1 : b⁻¹ * e * b ∈ E := by
      have := hBE b⁻¹ (B.inv_mem hb) e he
      simpa using this
    have h2 := mem_centralizer_iff.1 hm _ h1
    calc e * (b * m * b⁻¹) = b * ((b⁻¹ * e * b) * m) * b⁻¹ := by group
      _ = b * (m * (b⁻¹ * e * b)) * b⁻¹ := by rw [h2]
      _ = b * m * b⁻¹ * e := by group
  have hMBn : M ⊔ B ≤ normalizer (M : Set G) := by
    refine sup_le Subgroup.le_normalizer fun b hb => ?_
    rw [Subgroup.mem_normalizer_iff]
    intro m
    refine ⟨fun hm => hBM b hb m hm, fun hm => ?_⟩
    have := hBM b⁻¹ (B.inv_mem hb) _ hm
    simpa [mul_assoc] using this
  set MB : Subgroup G := M ⊔ B with hMBdef
  have hMleMB : M ≤ MB := le_sup_left
  have hBleMB : B ≤ MB := le_sup_right
  have hNnormal : (M.subgroupOf MB).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hMleMB).2 hMBn
  have hdecomp : ∀ g ∈ MB, ∃ m ∈ M, ∃ b ∈ B, g = m * b := by
    let K' : Subgroup G :=
      { carrier := {g | ∃ m ∈ M, ∃ b ∈ B, g = m * b}
        mul_mem' := by
          rintro _ _ ⟨m₁, hm₁, b₁, hb₁, rfl⟩ ⟨m₂, hm₂, b₂, hb₂, rfl⟩
          refine ⟨m₁ * (b₁ * m₂ * b₁⁻¹), M.mul_mem hm₁ (hBM b₁ hb₁ m₂ hm₂), b₁ * b₂,
            B.mul_mem hb₁ hb₂, by group⟩
        one_mem' := ⟨1, M.one_mem, 1, B.one_mem, by simp⟩
        inv_mem' := by
          rintro _ ⟨m, hm, b, hb, rfl⟩
          refine ⟨b⁻¹ * m⁻¹ * b, ?_, b⁻¹, B.inv_mem hb, by group⟩
          have := hBM b⁻¹ (B.inv_mem hb) m⁻¹ (M.inv_mem hm)
          simpa using this }
    have hle : MB ≤ K' := sup_le (fun m hm => ⟨m, hm, 1, B.one_mem, by simp⟩)
      (fun b hb => ⟨1, M.one_mem, b, hb, by simp⟩)
    intro g hg
    exact hle hg
  have := hNnormal
  have hQperf : ∀ k, derivedSeries (↥MB ⧸ M.subgroupOf MB) k = ⊤ := by
    obtain ⟨e⟩ := hB
    let φ : alternatingGroup (Fin 5) →* ↥MB ⧸ M.subgroupOf MB :=
      ((QuotientGroup.mk' (M.subgroupOf MB)).comp (Subgroup.inclusion hBleMB)).comp
        e.symm.toMonoidHom
    have hφ : Function.Surjective φ := by
      intro q
      obtain ⟨⟨g, hg⟩, rfl⟩ := QuotientGroup.mk_surjective q
      obtain ⟨m, hm, b, hb, rfl⟩ := hdecomp g hg
      refine ⟨e ⟨b, hb⟩, ?_⟩
      show QuotientGroup.mk (Subgroup.inclusion hBleMB (e.symm (e ⟨b, hb⟩))) = _
      simp only [MulEquiv.symm_apply_apply]
      rw [QuotientGroup.eq]
      show (b⁻¹ * (m * b) : G) ∈ M
      have := hBM b⁻¹ (B.inv_mem hb) m hm
      simpa [mul_assoc] using this
    have hA5 : Group.IsPerfect (alternatingGroup (Fin 5)) := isPerfect_alternatingGroup_five
    have : Group.IsPerfect (↥MB ⧸ M.subgroupOf MB) :=
      Group.IsPerfect.ofSurjective hφ (G := alternatingGroup (Fin 5))
    intro k
    exact Group.IsPerfect.derivedSeries_eq_top _ k
  have hFratt : ∀ g ∈ MB, ∃ m ∈ M, m * g ∈ normalizer (S : Set G) := by
    intro g hg
    have hgM : ∀ x ∈ M, g * x * g⁻¹ ∈ M ∧ g⁻¹ * x * g ∈ M := fun x hx => by
      refine ⟨(Subgroup.mem_normalizer_iff.1 (hMBn hg) x).1 hx, ?_⟩
      have := (Subgroup.mem_normalizer_iff.1 (hMBn (MB.inv_mem hg)) x).1 hx
      simpa using this
    let S' : Subgroup G := S.map (MulAut.conj g).toMonoidHom
    have hS'2 : IsPGroup 2 S' := hS2.map _
    have hS'M : S' ≤ M := by
      rintro _ ⟨s, hs, rfl⟩
      simpa [MulAut.conj_apply] using (hgM s (hSC hs)).1
    have hS'max : ∀ R : Subgroup G, IsPGroup 2 R → R ≤ M → S' ≤ R → R = S' := by
      intro R hR hRM hS'R
      let R' : Subgroup G := R.map (MulAut.conj g⁻¹).toMonoidHom
      have hR'2 : IsPGroup 2 R' := hR.map _
      have hR'M : R' ≤ M := by
        rintro _ ⟨r, hr, rfl⟩
        simpa [MulAut.conj_apply] using (hgM r (hRM hr)).2
      have hSR' : S ≤ R' := by
        intro s hs
        refine ⟨g * s * g⁻¹, hS'R ⟨s, hs, by simp [MulAut.conj_apply]⟩, ?_⟩
        simp
        group
      have hR'S : R' = S := hSmax R' hR'2 hR'M hSR'
      apply le_antisymm
      · intro r hr
        have : g⁻¹ * r * g ∈ S := by
          rw [← hR'S]
          exact ⟨r, hr, by simp⟩
        exact ⟨g⁻¹ * r * g, this, by simp [MulAut.conj_apply]; group⟩
      · exact hS'R
    obtain ⟨m, hmM, hm⟩ := exists_conj_of_maximal M hS2 hSC hSmax hS'2 hS'M hS'max
    refine ⟨m⁻¹, M.inv_mem hmM, ?_⟩
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have hx : x ∈ S ↔ g * x * g⁻¹ ∈ S' := by
      constructor
      · intro hxS
        exact ⟨x, hxS, by simp [MulAut.conj_apply]⟩
      · rintro ⟨s, hs, hsx⟩
        have : s = x := by simpa [MulAut.conj_apply] using hsx
        rw [← this]
        exact hs
    have heq : m⁻¹ * g * x * (m⁻¹ * g)⁻¹ = m⁻¹ * (g * x * g⁻¹) * m := by group
    rw [hx, hm, heq]
  set H : Subgroup ↥MB := (normalizer (S : Set G)).subgroupOf MB with hHdef
  have hNH : (M.subgroupOf MB) ⊔ H = ⊤ := by
    rw [eq_top_iff]
    intro p _
    obtain ⟨m, hmM, hmn⟩ := hFratt p.1 p.2
    have hmMB : m ∈ MB := hMleMB hmM
    have h1 : (⟨m, hmMB⟩ : ↥MB) ∈ M.subgroupOf MB := hmM
    have h2 : (⟨m * p.1, MB.mul_mem hmMB p.2⟩ : ↥MB) ∈ H := hmn
    have hp : p = (⟨m, hmMB⟩ : ↥MB)⁻¹ * ⟨m * p.1, MB.mul_mem hmMB p.2⟩ := by
      apply Subtype.ext
      simp
    rw [hp]
    exact mul_mem (inv_mem (mem_sup_left h1)) (mem_sup_right h2)
  let φ₀ : H →* normalizer (S : Set G) :=
    { toFun := fun c => ⟨(c.1 : G), c.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  let ρ : H →* MulAut ↥S := S.normalizerMonoidHom.comp φ₀
  have hlift := exists_lift_ker_of_solvable (M.subgroupOf MB) H hNH ρ hQperf
  have hker : ∀ c : H, ρ c = 1 → ∀ s ∈ S, (c.1 : G) * s * (c.1 : G)⁻¹ = s := by
    intro c hc s hs
    have := congrArg (fun f : MulAut ↥S => ((f ⟨s, hs⟩ : ↥S) : G)) hc
    simpa [ρ, φ₀] using this
  have hzM : z ∈ M := mem_centralizer_iff.2 fun e he => hzL e (hW.E_le he)
  have hVB : ∀ v, (v = 1 ∨ v = z ∨ v = t ∨ v = t * z) → ∀ b ∈ B, b * v = v * b := by
    intro v hv b hb
    have hbz : b * z = z * b := hzL b (hBL hb)
    have hbt : b * t = t * b := mem_centralizer_singleton_iff.1 (hBt hb)
    rcases hv with rfl | rfl | rfl | rfl
    · simp
    · exact hbz
    · exact hbt
    · rw [← mul_assoc, hbt, mul_assoc, hbz, mul_assoc]
  have hVV : ∀ v v', (v = 1 ∨ v = z ∨ v = t ∨ v = t * z) →
      (v' = 1 ∨ v' = z ∨ v' = t ∨ v' = t * z) → v * v' = v' * v := by
    have hc : Commute t z := htz
    have hV4 : ∀ v, (v = 1 ∨ v = z ∨ v = t ∨ v = t * z) → Commute v z ∧ Commute v t := by
      intro v hv
      rcases hv with rfl | rfl | rfl | rfl
      · exact ⟨Commute.one_left _, Commute.one_left _⟩
      · exact ⟨Commute.refl _, hc.symm⟩
      · exact ⟨hc, Commute.refl _⟩
      · exact ⟨hc.mul_left (Commute.refl _), (Commute.refl _).mul_left hc.symm⟩
    intro v v' hv hv'
    have h1 := hV4 v hv
    rcases hv' with rfl | rfl | rfl | rfl
    · exact (Commute.one_right _).eq
    · exact h1.1.eq
    · exact h1.2.eq
    · exact (h1.2.mul_right h1.1).eq
  have key : ∀ b ∈ B, ∃ v, (v = 1 ∨ v = z ∨ v = t ∨ v = t * z) ∧
      b * v ∈ centralizer (S : Set G) := by
    intro b hb
    obtain ⟨c, hcker, hcn⟩ := hlift ⟨b, hBleMB hb⟩
    have hgS := hker c hcker
    have hmM : (c.1 : G)⁻¹ * b ∈ M := hcn
    set g : G := (c.1 : G) with hgdef
    have hvM : b⁻¹ * g ∈ M := by
      have := M.inv_mem hmM
      simpa [mul_assoc] using this
    have hbv : b * (b⁻¹ * g) = g := by group
    have hzg : g * z * g⁻¹ = z := hgS z hzS
    have hbz : b * z = z * b := hzL b (hBL hb)
    have hvz : (b⁻¹ * g) * z = z * (b⁻¹ * g) := by
      have h1 : g * z = z * g := by
        calc g * z = (g * z * g⁻¹) * g := by group
          _ = z * g := by rw [hzg]
      calc b⁻¹ * g * z = b⁻¹ * (z * g) := by rw [mul_assoc, h1]
        _ = (b⁻¹ * z) * g := by group
        _ = (z * b⁻¹) * g := by
            have : b⁻¹ * z = z * b⁻¹ := by
              calc b⁻¹ * z = b⁻¹ * (z * b) * b⁻¹ := by group
                _ = b⁻¹ * (b * z) * b⁻¹ := by rw [hbz]
                _ = z * b⁻¹ := by group
            rw [this]
        _ = z * (b⁻¹ * g) := by group
    refine ⟨b⁻¹ * g, hV _ hvM hvz, ?_⟩
    rw [hbv]
    rw [mem_centralizer_iff]
    intro s hs
    have := hgS s hs
    calc s * g = (g * s * g⁻¹) * g := by rw [this]
      _ = g * s := by group
  have hcomm : ∀ b₁ ∈ B, ∀ b₂ ∈ B, b₁ * b₂ * b₁⁻¹ * b₂⁻¹ ∈ centralizer (S : Set G) := by
    intro b₁ hb₁ b₂ hb₂
    obtain ⟨v₁, hv₁, hc₁⟩ := key b₁ hb₁
    obtain ⟨v₂, hv₂, hc₂⟩ := key b₂ hb₂
    have e1 : v₁ * b₂ = b₂ * v₁ := (hVB v₁ hv₁ b₂ hb₂).symm
    have e2 : v₂ * b₁ = b₁ * v₂ := (hVB v₂ hv₂ b₁ hb₁).symm
    have e3 : v₁ * v₂ = v₂ * v₁ := hVV v₁ v₂ hv₁ hv₂
    have hval : (b₁ * v₁) * (b₂ * v₂) * (b₁ * v₁)⁻¹ * (b₂ * v₂)⁻¹ = b₁ * b₂ * b₁⁻¹ * b₂⁻¹ := by
      have e1' : v₁ * b₂⁻¹ = b₂⁻¹ * v₁ := by
        calc v₁ * b₂⁻¹ = b₂⁻¹ * (b₂ * v₁) * b₂⁻¹ := by group
          _ = b₂⁻¹ * (v₁ * b₂) * b₂⁻¹ := by rw [e1]
          _ = b₂⁻¹ * v₁ := by group
      have e2' : v₂ * b₁⁻¹ = b₁⁻¹ * v₂ := by
        calc v₂ * b₁⁻¹ = b₁⁻¹ * (b₁ * v₂) * b₁⁻¹ := by group
          _ = b₁⁻¹ * (v₂ * b₁) * b₁⁻¹ := by rw [e2]
          _ = b₁⁻¹ * v₂ := by group
      calc (b₁ * v₁) * (b₂ * v₂) * (b₁ * v₁)⁻¹ * (b₂ * v₂)⁻¹
          = b₁ * (v₁ * b₂) * (v₂ * v₁⁻¹) * b₁⁻¹ * v₂⁻¹ * b₂⁻¹ := by group
        _ = b₁ * (b₂ * v₁) * (v₁⁻¹ * v₂) * b₁⁻¹ * v₂⁻¹ * b₂⁻¹ := by
            rw [e1, show v₂ * v₁⁻¹ = v₁⁻¹ * v₂ by
              calc v₂ * v₁⁻¹ = v₁⁻¹ * (v₁ * v₂) * v₁⁻¹ := by group
                _ = v₁⁻¹ * (v₂ * v₁) * v₁⁻¹ := by rw [e3]
                _ = v₁⁻¹ * v₂ := by group]
        _ = b₁ * b₂ * v₂ * b₁⁻¹ * v₂⁻¹ * b₂⁻¹ := by group
        _ = b₁ * b₂ * (v₂ * b₁⁻¹) * v₂⁻¹ * b₂⁻¹ := by group
        _ = b₁ * b₂ * (b₁⁻¹ * v₂) * v₂⁻¹ * b₂⁻¹ := by rw [e2']
        _ = b₁ * b₂ * b₁⁻¹ * b₂⁻¹ := by group
    rw [← hval]
    have hc₁' := hc₁
    have hc₂' := hc₂
    exact (centralizer (S : Set G)).mul_mem
      ((centralizer (S : Set G)).mul_mem
        ((centralizer (S : Set G)).mul_mem hc₁ hc₂) ((centralizer (S : Set G)).inv_mem hc₁))
      ((centralizer (S : Set G)).inv_mem hc₂)
  obtain ⟨e⟩ := hB
  have hA5 : Group.IsPerfect (alternatingGroup (Fin 5)) := isPerfect_alternatingGroup_five
  have hBperf : Group.IsPerfect ↥B :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hBB : ⁅B, B⁆ = B := Subgroup.commutator_eq_self
  have hle : ⁅B, B⁆ ≤ centralizer (S : Set G) :=
    Subgroup.commutator_le.2 fun b₁ hb₁ b₂ hb₂ => hcomm b₁ hb₁ b₂ hb₂
  intro b hb s hs
  have : b ∈ centralizer (S : Set G) := hle (by rw [hBB]; exact hb)
  exact (mem_centralizer_iff.1 this s hs).symm

end CFSG.EvenSporadicStandard.Fin76b
