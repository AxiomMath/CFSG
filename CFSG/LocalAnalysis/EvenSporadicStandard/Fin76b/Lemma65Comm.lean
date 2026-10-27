module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.WFacts
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.CentE

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup
open scoped Pointwise

theorem isPerfect_alternatingGroup_five : Group.IsPerfect (alternatingGroup (Fin 5)) := by
  have hs : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  rw [Group.isPerfect_def]
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator (alternatingGroup (Fin 5))) with
    h | h
  · exfalso
    let a : alternatingGroup (Fin 5) :=
      ⟨Equiv.swap 0 1 * Equiv.swap 2 3, by
        rw [Equiv.Perm.mem_alternatingGroup]; simp [Equiv.Perm.sign_mul]⟩
    let b : alternatingGroup (Fin 5) :=
      ⟨Equiv.swap 1 2 * Equiv.swap 3 4, by
        rw [Equiv.Perm.mem_alternatingGroup]; simp [Equiv.Perm.sign_mul]⟩
    have hab : a * b ≠ b * a := by
      intro hh
      have := congrArg Subtype.val hh
      revert this
      decide
    apply hab
    have hmem : a * b * a⁻¹ * b⁻¹ ∈ commutator (alternatingGroup (Fin 5)) :=
      commutator_mem_commutator (mem_top a) (mem_top b)
    rw [h, mem_bot] at hmem
    calc a * b = (a * b * a⁻¹ * b⁻¹) * (b * a) := by group
      _ = b * a := by rw [hmem, one_mul]
  · exact h

theorem exists_lift_ker_of_solvable {P Γ : Type*} [Group P] [Group Γ] [Group.IsSolvable Γ]
    (N : Subgroup P) [N.Normal] (H : Subgroup P) (hNH : N ⊔ H = ⊤) (ρ : H →* Γ)
    (hperf : ∀ k, derivedSeries (P ⧸ N) k = ⊤) :
    ∀ x : P, ∃ c : H, ρ c = 1 ∧ (c : P)⁻¹ * x ∈ N := by
  intro x
  let πH : H →* P ⧸ N := (QuotientGroup.mk' N).comp H.subtype
  have hsurj : Function.Surjective πH := by
    intro q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
    have hy : y ∈ ((N ⊔ H : Subgroup P) : Set P) := by rw [hNH]; trivial
    rw [Subgroup.normal_mul] at hy
    obtain ⟨n, hn, h, hh, rfl⟩ := hy
    refine ⟨⟨h, hh⟩, ?_⟩
    show QuotientGroup.mk h = QuotientGroup.mk (n * h)
    rw [QuotientGroup.eq]
    have := (inferInstance : N.Normal).conj_mem n hn h⁻¹
    simpa [mul_assoc] using this
  obtain ⟨k, hk⟩ := Group.IsSolvable.solvable (G := Γ)
  have h1 := map_derivedSeries_le_derivedSeries ρ k
  have h2 := map_derivedSeries_eq hsurj k
  rw [hperf k] at h2
  have hxq : (QuotientGroup.mk x : P ⧸ N) ∈ (derivedSeries H k).map πH := by rw [h2]; trivial
  obtain ⟨c, hc, hcx⟩ := hxq
  refine ⟨c, ?_, ?_⟩
  · have : ρ c ∈ derivedSeries Γ k := h1 ⟨c, hc, rfl⟩
    rw [hk] at this
    exact this
  · have : (QuotientGroup.mk (c : P) : P ⧸ N) = QuotientGroup.mk x := hcx
    exact QuotientGroup.eq.1 this

variable {G : Type*} [Group G] [Finite G]

@[expose] def sylowOfMaximal (M S : Subgroup G) (hS2 : IsPGroup 2 S) (hSM : S ≤ M)
    (hmax : ∀ R : Subgroup G, IsPGroup 2 R → R ≤ M → S ≤ R → R = S) : Sylow 2 M where
  toSubgroup := S.subgroupOf M
  isPGroup' := hS2.comap_subtype
  is_maximal' := by
    intro Q hQ hSQ
    have hR : Q.map M.subtype = S := by
      refine hmax _ (hQ.map _) (by rintro _ ⟨q, -, rfl⟩; exact q.2) ?_
      intro s hs
      exact ⟨⟨s, hSM hs⟩, hSQ (mem_subgroupOf.2 hs), rfl⟩
    ext x
    constructor
    · intro hx
      show (x : G) ∈ S
      rw [← hR]
      exact ⟨x, hx, rfl⟩
    · intro hx
      exact hSQ hx

theorem exists_conj_of_maximal (M : Subgroup G) {S₁ S₂ : Subgroup G} (h1 : IsPGroup 2 S₁)
    (h1M : S₁ ≤ M) (h1m : ∀ R : Subgroup G, IsPGroup 2 R → R ≤ M → S₁ ≤ R → R = S₁)
    (h2 : IsPGroup 2 S₂) (h2M : S₂ ≤ M)
    (h2m : ∀ R : Subgroup G, IsPGroup 2 R → R ≤ M → S₂ ≤ R → R = S₂) :
    ∃ m ∈ M, ∀ x : G, x ∈ S₂ ↔ m⁻¹ * x * m ∈ S₁ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq M (sylowOfMaximal M S₁ h1 h1M h1m)
    (sylowOfMaximal M S₂ h2 h2M h2m)
  refine ⟨g, g.2, fun x => ?_⟩
  constructor
  · intro hx
    have hxM : x ∈ M := h2M hx
    have : (⟨x, hxM⟩ : M) ∈ ((g • sylowOfMaximal M S₁ h1 h1M h1m : Sylow 2 M) : Subgroup M) := by
      rw [hg]; exact hx
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at this
    obtain ⟨s, hs, hsx⟩ := this
    have hs' : (s : G) ∈ S₁ := hs
    have : g⁻¹ * (⟨x, hxM⟩ : M) * g = s := by
      rw [← hsx, MulAut.smul_def, MulAut.conj_apply]; group
    have h3 := congrArg Subtype.val this
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h3
    rw [h3]
    exact hs'
  · intro hx
    have hxM : x ∈ M := by
      have h4 : (g : G)⁻¹ * x * g ∈ M := h1M hx
      have := M.mul_mem (M.mul_mem g.2 h4) (M.inv_mem g.2)
      simpa [mul_assoc] using this
    have : (⟨x, hxM⟩ : M) ∈ ((g • sylowOfMaximal M S₁ h1 h1M h1m : Sylow 2 M) : Subgroup M) := by
      rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists]
      refine ⟨g⁻¹ * ⟨x, hxM⟩ * g, hx, ?_⟩
      rw [MulAut.smul_def, MulAut.conj_apply]; group
    rw [hg] at this
    exact this

variable {L : Subgroup G} {z t : G} {T₀ E : Subgroup G}

theorem B_centralizes_S (h : InnerConfig G L z t T₀) (hE : EConfig L T₀ E t)
    (hW : WFacts L t E) {B : Subgroup G} (hBL : B ≤ L) (hBt : B ≤ centralizer ({t} : Set G))
    (hB : Nonempty (↥B ≃* alternatingGroup (Fin 5))) {S : Subgroup G} (hS2 : IsPGroup 2 S)
    (hSC : S ≤ centralizer (E : Set G))
    (hSmax : ∀ R : Subgroup G, IsPGroup 2 R → R ≤ centralizer (E : Set G) → S ≤ R → R = S)
    (hzS : z ∈ S) [Group.IsSolvable (MulAut ↥S)] : ∀ b ∈ B, ∀ s ∈ S, b * s = s * b := by
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
  have hzM : z ∈ M := hE.z_mem_centralizer h
  have hV : ∀ v ∈ M, v * z = z * v → v = 1 ∨ v = z ∨ v = t ∨ v = t * z := by
    intro v hvM hvz
    have hv' : v ∈ L ⊔ zpowers z := by
      rw [← h.cent_eq]
      exact mem_centralizer_singleton_iff.2 hvz
    obtain ⟨l, hl, c, hc, hvlc⟩ :=
      exists_mul_of_mem_sup_of_le_centralizer (zpowers_le.2 h.z_cent) hv'
    have hcM : c ∈ M := by
      rcases mem_zpowers_sq_eq_one h.z_sq hc with rfl | rfl
      · exact M.one_mem
      · exact hzM
    have hlM : l ∈ M := by
      have : l = v * c⁻¹ := by rw [hvlc]; group
      rw [this]
      exact M.mul_mem hvM (M.inv_mem hcM)
    have hl' : l = 1 ∨ l = t :=
      hW.cent l hl (fun e he => (mem_centralizer_iff.1 hlM e he).symm)
    rcases mem_zpowers_sq_eq_one h.z_sq hc with rfl | rfl <;> rcases hl' with rfl | rfl <;>
      simp [hvlc]
  have hVB : ∀ v, (v = 1 ∨ v = z ∨ v = t ∨ v = t * z) → ∀ b ∈ B, b * v = v * b := by
    intro v hv b hb
    have hbz : b * z = z * b := h.z_comm_of_mem_A (hBL hb)
    have hbt : b * t = t * b := mem_centralizer_singleton_iff.1 (hBt hb)
    rcases hv with rfl | rfl | rfl | rfl
    · simp
    · exact hbz
    · exact hbt
    · rw [← mul_assoc, hbt, mul_assoc, hbz, mul_assoc]
  have hVV : ∀ v v', (v = 1 ∨ v = z ∨ v = t ∨ v = t * z) →
      (v' = 1 ∨ v' = z ∨ v' = t ∨ v' = t * z) → v * v' = v' * v := by
    have hc : Commute t z := h.t_comm_z
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
    have hbz : b * z = z * b := h.z_comm_of_mem_A (hBL hb)
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
