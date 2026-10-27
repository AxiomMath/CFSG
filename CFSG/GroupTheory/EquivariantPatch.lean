module

public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Algebra.Group.End
public import Mathlib.GroupTheory.GroupAction.Defs
public import Mathlib.Order.ConditionallyCompleteLattice.Basic

public section

namespace CFSG.GroupTheory

variable {H H' Ω Ω' : Type*} [Group H] [Group H'] [MulAction H Ω] [MulAction H' Ω']

open scoped Classical in
private noncomputable def patchValue {B S : Set Ω} (θ : H ≃* H') (f₀ ψ : Ω → Ω')
    (hcov : ∀ x ∉ B, ∃ h : H, ∃ s ∈ S, h • s = x) (x : Ω) : Ω' :=
  if hx : x ∈ B then f₀ x
  else θ (Classical.choose (hcov x hx)) •
    ψ (Classical.choose (Classical.choose_spec (hcov x hx)))

private lemma patchValue_of_mem {B S : Set Ω} (θ : H ≃* H') (f₀ ψ : Ω → Ω')
    (hcov : ∀ x ∉ B, ∃ h : H, ∃ s ∈ S, h • s = x) {x : Ω} (hx : x ∈ B) :
    patchValue θ f₀ ψ hcov x = f₀ x := by
  rw [patchValue, dif_pos hx]

private lemma patchValue_of_notMem {B S : Set Ω} (θ : H ≃* H') (f₀ ψ : Ω → Ω')
    (hcov : ∀ x ∉ B, ∃ h : H, ∃ s ∈ S, h • s = x) {x : Ω} (hx : x ∉ B) :
    patchValue θ f₀ ψ hcov x =
      θ (Classical.choose (hcov x hx)) •
        ψ (Classical.choose (Classical.choose_spec (hcov x hx))) := by
  rw [patchValue, dif_neg hx]

private lemma smul_psi_eq_of_smul_eq (θ : H ≃* H') (R : Subgroup H)
    {S : Set Ω} {ψ : Ω → Ω'}
    (hψθ : ∀ r ∈ R, ∀ s ∈ S, ψ (r • s) = θ r • ψ s)
    (hstab : ∀ s ∈ S,
      (MulAction.stabilizer H s).map θ.toMonoidHom = MulAction.stabilizer H' (ψ s))
    (hfus : ∀ s ∈ S, ∀ h : H, h • s ∈ S → ∃ r ∈ R, r • s = h • s)
    {s t : Ω} (hs : s ∈ S) (ht : t ∈ S) {h k : H} (h_eq : h • s = k • t) :
    θ h • ψ s = θ k • ψ t := by
  have h_ks : (k⁻¹ * h) • s = t := by
    rw [mul_smul, h_eq, inv_smul_smul]
  obtain ⟨r, hrR, hr⟩ := hfus s hs (k⁻¹ * h) (by rw [h_ks]; exact ht)
  have hg_stab : (k⁻¹ * h)⁻¹ * r ∈ MulAction.stabilizer H s := by
    rw [MulAction.mem_stabilizer_iff, mul_smul, hr, inv_smul_smul]
  have hg_stab' : θ ((k⁻¹ * h)⁻¹ * r) ∈ MulAction.stabilizer H' (ψ s) := by
    rw [← hstab s hs]
    exact Subgroup.mem_map_of_mem θ.toMonoidHom hg_stab
  have hg_psi : θ ((k⁻¹ * h)⁻¹ * r) • ψ s = ψ s :=
    MulAction.mem_stabilizer_iff.mp hg_stab'
  have hC : θ r • ψ s = θ (k⁻¹ * h) • ψ s := by
    calc
      θ r • ψ s = θ ((k⁻¹ * h) * ((k⁻¹ * h)⁻¹ * r)) • ψ s := by
        rw [mul_inv_cancel_left]
      _ = θ (k⁻¹ * h) • (θ ((k⁻¹ * h)⁻¹ * r) • ψ s) := by
        rw [map_mul, mul_smul]
      _ = θ (k⁻¹ * h) • ψ s := by rw [hg_psi]
  have ht_rs : t = r • s := h_ks.symm.trans hr.symm
  have hpsi_t : ψ t = θ r • ψ s := by rw [ht_rs, hψθ r hrR s hs]
  calc
    θ h • ψ s = θ (k * (k⁻¹ * h)) • ψ s := by rw [mul_inv_cancel_left]
    _ = (θ k * θ (k⁻¹ * h)) • ψ s := by rw [map_mul, mul_smul]
    _ = θ k • (θ (k⁻¹ * h) • ψ s) := by rw [mul_smul]
    _ = θ k • ψ t := by rw [← hC, ← hpsi_t]

private lemma patchValue_of_smul (θ : H ≃* H') (R : Subgroup H) {B S : Set Ω}
    {ψ : Ω → Ω'} {f₀ : Ω → Ω'}
    (hB : ∀ h : H, ∀ x ∈ B, h • x ∈ B) (hSB : Disjoint S B)
    (hcov : ∀ x ∉ B, ∃ h : H, ∃ s ∈ S, h • s = x)
    (hψθ : ∀ r ∈ R, ∀ s ∈ S, ψ (r • s) = θ r • ψ s)
    (hstab : ∀ s ∈ S,
      (MulAction.stabilizer H s).map θ.toMonoidHom = MulAction.stabilizer H' (ψ s))
    (hfus : ∀ s ∈ S, ∀ h : H, h • s ∈ S → ∃ r ∈ R, r • s = h • s)
    (h : H) (s : Ω) (hs : s ∈ S) (x : Ω) (hx : h • s = x) :
    patchValue θ f₀ ψ hcov x = θ h • ψ s := by
  have hxB : x ∉ B := by
    intro hxB
    have hsB : s ∈ B := by
      have := hB h⁻¹ x hxB
      rwa [← hx, inv_smul_smul] at this
    exact Set.disjoint_left.mp hSB hs hsB
  rw [patchValue_of_notMem θ f₀ ψ hcov hxB]
  let k := Classical.choose (hcov x hxB)
  let t := Classical.choose (Classical.choose_spec (hcov x hxB))
  have ht : t ∈ S := (Classical.choose_spec (Classical.choose_spec (hcov x hxB))).1
  have hkt : k • t = x := (Classical.choose_spec (Classical.choose_spec (hcov x hxB))).2
  exact smul_psi_eq_of_smul_eq θ R hψθ hstab hfus ht hs (hkt.trans hx.symm)

private lemma image_invariant (θ : H ≃* H') {B : Set Ω} {B' : Set Ω'} {f₀ : Ω → Ω'}
    (hB : ∀ h : H, ∀ x ∈ B, h • x ∈ B) (hf₀ : Set.BijOn f₀ B B')
    (hf₀θ : ∀ h : H, ∀ x ∈ B, f₀ (h • x) = θ h • f₀ x) :
    ∀ h' : H', ∀ y ∈ B', h' • y ∈ B' := by
  intro h' y hy
  obtain ⟨b, hb, rfl⟩ := hf₀.surjOn hy
  have h := hf₀θ (θ.symm h') b hb
  rw [θ.apply_symm_apply] at h
  rw [← h]
  exact hf₀.mapsTo (hB (θ.symm h') b hb)

private lemma patchValue_mem_image_iff (θ : H ≃* H') {B S : Set Ω} {B' S' : Set Ω'}
    {f₀ ψ : Ω → Ω'}
    (hB : ∀ h : H, ∀ x ∈ B, h • x ∈ B) (hf₀ : Set.BijOn f₀ B B')
    (hf₀θ : ∀ h : H, ∀ x ∈ B, f₀ (h • x) = θ h • f₀ x)
    (hSB' : Disjoint S' B') (hψ : Set.BijOn ψ S S')
    (hcov : ∀ x ∉ B, ∃ h : H, ∃ s ∈ S, h • s = x)
    (hval : ∀ (h : H) (s : Ω) (x : Ω), s ∈ S → h • s = x →
      patchValue θ f₀ ψ hcov x = θ h • ψ s)
    (x : Ω) : patchValue θ f₀ ψ hcov x ∈ B' ↔ x ∈ B := by
  constructor
  · intro hxB'
    by_contra hx
    let h := Classical.choose (hcov x hx)
    let s := Classical.choose (Classical.choose_spec (hcov x hx))
    have hs : s ∈ S := (Classical.choose_spec (Classical.choose_spec (hcov x hx))).1
    have hh : h • s = x := (Classical.choose_spec (Classical.choose_spec (hcov x hx))).2
    have hψs : ψ s ∈ S' := hψ.mapsTo hs
    have hnot : θ h • ψ s ∉ B' := by
      intro hmem
      have := image_invariant θ hB hf₀ hf₀θ (θ h)⁻¹ (θ h • ψ s) hmem
      rw [inv_smul_smul] at this
      exact Set.disjoint_left.mp hSB' hψs this
    rw [hval h s x hs hh] at hxB'
    exact hnot hxB'
  · intro hx
    rw [patchValue_of_mem θ f₀ ψ hcov hx]
    exact hf₀.mapsTo hx

private lemma patchValue_equivariant (θ : H ≃* H') {B S : Set Ω}
    {f₀ ψ : Ω → Ω'}
    (hB : ∀ h : H, ∀ x ∈ B, h • x ∈ B)
    (hf₀θ : ∀ h : H, ∀ x ∈ B, f₀ (h • x) = θ h • f₀ x)
    (hcov : ∀ x ∉ B, ∃ h : H, ∃ s ∈ S, h • s = x)
    (hval : ∀ (h : H) (s : Ω) (x : Ω), s ∈ S → h • s = x →
      patchValue θ f₀ ψ hcov x = θ h • ψ s) :
    ∀ (g : H) (x : Ω), patchValue θ f₀ ψ hcov (g • x) = θ g •
      patchValue θ f₀ ψ hcov x := by
  intro g x
  by_cases hx : x ∈ B
  · rw [patchValue_of_mem θ f₀ ψ hcov (hB g x hx),
      patchValue_of_mem θ f₀ ψ hcov hx, hf₀θ g x hx]
  · let h := Classical.choose (hcov x hx)
    let s := Classical.choose (Classical.choose_spec (hcov x hx))
    have hs : s ∈ S := (Classical.choose_spec (Classical.choose_spec (hcov x hx))).1
    have hh : h • s = x := (Classical.choose_spec (Classical.choose_spec (hcov x hx))).2
    have hgx : g • x ∉ B := by
      intro hgxB
      exact hx (by simpa using hB g⁻¹ (g • x) hgxB)
    rw [hval (g * h) s (g • x) hs (by rw [mul_smul, hh]), hval h s x hs hh,
      map_mul, mul_smul]

private lemma smul_eq_of_psi_smul_eq (θ : H ≃* H') (R : Subgroup H)
    {S : Set Ω} {S' : Set Ω'} {ψ : Ω → Ω'} (hψ : Set.BijOn ψ S S')
    (hRS : ∀ r ∈ R, ∀ s ∈ S, r • s ∈ S)
    (hψθ : ∀ r ∈ R, ∀ s ∈ S, ψ (r • s) = θ r • ψ s)
    (hstab : ∀ s ∈ S,
      (MulAction.stabilizer H s).map θ.toMonoidHom = MulAction.stabilizer H' (ψ s))
    (hfus' : ∀ s ∈ S', ∀ h : H', h • s ∈ S' →
      ∃ r ∈ R.map θ.toMonoidHom, r • s = h • s)
    {s t : Ω} (hs : s ∈ S) (ht : t ∈ S) {h k : H}
    (h_eq : θ h • ψ s = θ k • ψ t) : h • s = k • t := by
  have hstep : θ (k⁻¹ * h) • ψ s = ψ t := by
    have := congrArg (fun z => (θ k)⁻¹ • z) h_eq
    simpa [← map_mul, ← map_inv, smul_smul] using this
  have hψs : ψ s ∈ S' := hψ.mapsTo hs
  have hψt : ψ t ∈ S' := hψ.mapsTo ht
  obtain ⟨r', hr'R, hr'⟩ := hfus' (ψ s) hψs (θ (k⁻¹ * h)) (by rw [hstep]; exact hψt)
  obtain ⟨r, hrR, rfl⟩ := (Subgroup.mem_map.mp hr'R)
  change θ r • ψ s = θ (k⁻¹ * h) • ψ s at hr'
  have hψr : ψ (r • s) = ψ t := by rw [hψθ r hrR s hs, hr', hstep]
  have hrs : r • s ∈ S := hRS r hrR s hs
  have hrst : r • s = t := hψ.injOn hrs ht hψr
  have hg_stab' : θ ((k⁻¹ * h)⁻¹ * r) ∈ MulAction.stabilizer H' (ψ s) := by
    rw [MulAction.mem_stabilizer_iff]
    calc
      θ ((k⁻¹ * h)⁻¹ * r) • ψ s = (θ (k⁻¹ * h))⁻¹ • (θ r • ψ s) := by
        rw [map_mul, map_inv, mul_smul]
      _ = (θ (k⁻¹ * h))⁻¹ • (θ (k⁻¹ * h) • ψ s) := by rw [hr']
      _ = ψ s := inv_smul_smul _ _
  have hg_mem : θ ((k⁻¹ * h)⁻¹ * r) ∈
      (MulAction.stabilizer H s).map θ.toMonoidHom := by
    rw [hstab s hs]
    exact hg_stab'
  obtain ⟨a, ha, haeq⟩ := (Subgroup.mem_map.mp hg_mem)
  have hga : a = (k⁻¹ * h)⁻¹ * r := θ.injective haeq
  have hg_s : ((k⁻¹ * h)⁻¹ * r) • s = s := by
    rw [hga] at ha
    exact MulAction.mem_stabilizer_iff.mp ha
  have ht_eq : t = (k⁻¹ * h) • s := by
    have hstep' := hg_s
    rw [mul_smul, hrst] at hstep'
    calc
      t = (k⁻¹ * h) • ((k⁻¹ * h)⁻¹ • t) :=
        (smul_inv_smul (k⁻¹ * h) t).symm
      _ = (k⁻¹ * h) • s := by rw [hstep']
  calc
    h • s = (k * (k⁻¹ * h)) • s := by rw [mul_inv_cancel_left]
    _ = k • ((k⁻¹ * h) • s) := by rw [mul_smul]
    _ = k • t := by rw [ht_eq]

private lemma eq_of_patchValue_eq_of_notMem (θ : H ≃* H') (R : Subgroup H)
    {B S : Set Ω} {S' : Set Ω'} {f₀ ψ : Ω → Ω'}
    (hψ : Set.BijOn ψ S S') (hRS : ∀ r ∈ R, ∀ s ∈ S, r • s ∈ S)
    (hψθ : ∀ r ∈ R, ∀ s ∈ S, ψ (r • s) = θ r • ψ s)
    (hstab : ∀ s ∈ S,
      (MulAction.stabilizer H s).map θ.toMonoidHom = MulAction.stabilizer H' (ψ s))
    (hfus' : ∀ s ∈ S', ∀ h : H', h • s ∈ S' →
      ∃ r ∈ R.map θ.toMonoidHom, r • s = h • s)
    (hcov : ∀ x ∉ B, ∃ h : H, ∃ s ∈ S, h • s = x)
    (hval : ∀ (h : H) (s : Ω) (x : Ω), s ∈ S → h • s = x →
      patchValue θ f₀ ψ hcov x = θ h • ψ s)
    {x y : Ω} (hx : x ∉ B) (hy : y ∉ B)
    (hxy : patchValue θ f₀ ψ hcov x = patchValue θ f₀ ψ hcov y) : x = y := by
  let h := Classical.choose (hcov x hx)
  let s := Classical.choose (Classical.choose_spec (hcov x hx))
  let k := Classical.choose (hcov y hy)
  let t := Classical.choose (Classical.choose_spec (hcov y hy))
  have hs : s ∈ S := (Classical.choose_spec (Classical.choose_spec (hcov x hx))).1
  have hh : h • s = x := (Classical.choose_spec (Classical.choose_spec (hcov x hx))).2
  have ht : t ∈ S := (Classical.choose_spec (Classical.choose_spec (hcov y hy))).1
  have hk : k • t = y := (Classical.choose_spec (Classical.choose_spec (hcov y hy))).2
  have hF : θ h • ψ s = θ k • ψ t := by
    rw [← hval h s x hs hh, ← hval k t y ht hk]
    exact hxy
  have hst : h • s = k • t :=
    smul_eq_of_psi_smul_eq θ R hψ hRS hψθ hstab hfus' hs ht hF
  calc
    x = h • s := hh.symm
    _ = k • t := hst
    _ = y := hk

private lemma patchValue_injective (θ : H ≃* H') (R : Subgroup H) {B S : Set Ω}
    {B' S' : Set Ω'} {f₀ ψ : Ω → Ω'}
    (hB : ∀ h : H, ∀ x ∈ B, h • x ∈ B) (hf₀ : Set.BijOn f₀ B B')
    (hf₀θ : ∀ h : H, ∀ x ∈ B, f₀ (h • x) = θ h • f₀ x)
    (hSB' : Disjoint S' B') (hψ : Set.BijOn ψ S S')
    (hRS : ∀ r ∈ R, ∀ s ∈ S, r • s ∈ S)
    (hψθ : ∀ r ∈ R, ∀ s ∈ S, ψ (r • s) = θ r • ψ s)
    (hstab : ∀ s ∈ S,
      (MulAction.stabilizer H s).map θ.toMonoidHom = MulAction.stabilizer H' (ψ s))
    (hfus' : ∀ s ∈ S', ∀ h : H', h • s ∈ S' →
      ∃ r ∈ R.map θ.toMonoidHom, r • s = h • s)
    (hcov : ∀ x ∉ B, ∃ h : H, ∃ s ∈ S, h • s = x)
    (hval : ∀ (h : H) (s : Ω) (x : Ω), s ∈ S → h • s = x →
      patchValue θ f₀ ψ hcov x = θ h • ψ s) :
    Function.Injective (patchValue θ f₀ ψ hcov) := by
  intro x y hxy
  have hbase := patchValue_mem_image_iff θ hB hf₀ hf₀θ hSB' hψ hcov hval
  by_cases hx : x ∈ B
  · by_cases hy : y ∈ B
    · apply hf₀.injOn hx hy
      rwa [patchValue_of_mem θ f₀ ψ hcov hx,
        patchValue_of_mem θ f₀ ψ hcov hy] at hxy
    · have hxF : patchValue θ f₀ ψ hcov x ∈ B' := (hbase x).2 hx
      have hyF : patchValue θ f₀ ψ hcov y ∉ B' :=
        fun hmem => hy ((hbase y).mp hmem)
      exact absurd (by rw [← hxy]; exact hxF) hyF
  · by_cases hy : y ∈ B
    · have hxF : patchValue θ f₀ ψ hcov x ∉ B' :=
        fun hmem => hx ((hbase x).mp hmem)
      have hyF : patchValue θ f₀ ψ hcov y ∈ B' := (hbase y).2 hy
      exact absurd (by rw [hxy]; exact hyF) hxF
    · exact eq_of_patchValue_eq_of_notMem θ R hψ hRS hψθ hstab hfus' hcov hval hx hy hxy

private lemma patchValue_surjective (θ : H ≃* H') {B S : Set Ω} {B' S' : Set Ω'}
    {f₀ ψ : Ω → Ω'}
    (hB : ∀ h : H, ∀ x ∈ B, h • x ∈ B) (hSB : Disjoint S B)
    (hf₀ : Set.BijOn f₀ B B') (hψ : Set.BijOn ψ S S')
    (hcov : ∀ x ∉ B, ∃ h : H, ∃ s ∈ S, h • s = x)
    (hcov' : ∀ x ∉ B', ∃ h : H', ∃ s ∈ S', h • s = x)
    (hval : ∀ (h : H) (s : Ω) (x : Ω), s ∈ S → h • s = x →
      patchValue θ f₀ ψ hcov x = θ h • ψ s) :
    Function.Surjective (patchValue θ f₀ ψ hcov) := by
  intro y
  by_cases hy : y ∈ B'
  · obtain ⟨b, hb, rfl⟩ := hf₀.surjOn hy
    exact ⟨b, patchValue_of_mem θ f₀ ψ hcov hb⟩
  · obtain ⟨h', s', hs', hh'⟩ := hcov' y hy
    obtain ⟨s, hs, rfl⟩ := hψ.surjOn hs'
    let h := θ.symm h'
    refine ⟨h • s, ?_⟩
    have hxB : h • s ∉ B := by
      intro hxB
      have hsB : s ∈ B := by simpa using hB h⁻¹ (h • s) hxB
      exact Set.disjoint_left.mp hSB hs hsB
    rw [hval h s (h • s) hs rfl, θ.apply_symm_apply, hh']

theorem exists_equivariant_equiv_of_patch (θ : H ≃* H') (R : Subgroup H)
    {B S : Set Ω} {B' S' : Set Ω'} (f₀ ψ : Ω → Ω')
    (hB : ∀ h : H, ∀ x ∈ B, h • x ∈ B) (hf₀ : Set.BijOn f₀ B B')
    (hf₀θ : ∀ h : H, ∀ x ∈ B, f₀ (h • x) = θ h • f₀ x)
    (hSB : Disjoint S B) (hSB' : Disjoint S' B')
    (hψ : Set.BijOn ψ S S') (hRS : ∀ r ∈ R, ∀ s ∈ S, r • s ∈ S)
    (hψθ : ∀ r ∈ R, ∀ s ∈ S, ψ (r • s) = θ r • ψ s)
    (hcov : ∀ x ∉ B, ∃ h : H, ∃ s ∈ S, h • s = x)
    (hcov' : ∀ x ∉ B', ∃ h : H', ∃ s ∈ S', h • s = x)
    (hstab : ∀ s ∈ S,
      (MulAction.stabilizer H s).map θ.toMonoidHom = MulAction.stabilizer H' (ψ s))
    (hfus : ∀ s ∈ S, ∀ h : H, h • s ∈ S → ∃ r ∈ R, r • s = h • s)
    (hfus' : ∀ s ∈ S', ∀ h : H', h • s ∈ S' → ∃ r ∈ R.map θ.toMonoidHom, r • s = h • s) :
    ∃ F : Ω ≃ Ω', (∀ (h : H) (x : Ω), F (h • x) = θ h • F x) ∧ (∀ x ∈ B, F x = f₀ x) ∧
      ∀ s ∈ S, F s = ψ s := by
  let F := patchValue θ f₀ ψ hcov
  have hval : ∀ (h : H) (s : Ω) (x : Ω), s ∈ S → h • s = x → F x = θ h • ψ s :=
    fun h s x hs hx =>
      patchValue_of_smul θ R hB hSB hcov hψθ hstab hfus h s hs x hx
  have heq : ∀ (g : H) (x : Ω), F (g • x) = θ g • F x :=
    patchValue_equivariant θ hB hf₀θ hcov hval
  have hinj : Function.Injective F :=
    patchValue_injective θ R hB hf₀ hf₀θ hSB' hψ hRS hψθ hstab hfus' hcov hval
  have hsurj : Function.Surjective F :=
    patchValue_surjective θ hB hSB hf₀ hψ hcov hcov' hval
  refine ⟨Equiv.ofBijective F (show Function.Bijective F from ⟨hinj, hsurj⟩), ?_, ?_, ?_⟩
  · intro h x
    rw [Equiv.coe_ofBijective]
    exact heq h x
  · intro x hx
    rw [Equiv.coe_ofBijective]
    exact patchValue_of_mem θ f₀ ψ hcov hx
  · intro s hs
    rw [Equiv.coe_ofBijective]
    simpa using hval 1 s s hs (one_smul H s)

theorem adj_iff_of_equivariant_of_patch (θ : H ≃* H') (F : Ω ≃ Ω')
    (hF : ∀ (h : H) (x : Ω), F (h • x) = θ h • F x)
    (Γ : SimpleGraph Ω) (Γ' : SimpleGraph Ω')
    (hΓ : ∀ (h : H) (x y : Ω), Γ.Adj x y → Γ.Adj (h • x) (h • y))
    (hΓ' : ∀ (h : H') (x y : Ω'), Γ'.Adj x y → Γ'.Adj (h • x) (h • y))
    (P : Set Ω) (hP : ∀ x ∈ P, ∀ y ∈ P, Γ.Adj x y ↔ Γ'.Adj (F x) (F y))
    (hcov : ∀ x y : Ω, Γ.Adj x y → ∃ h : H, h • x ∈ P ∧ h • y ∈ P)
    (hcov' : ∀ x y : Ω', Γ'.Adj x y → ∃ h : H', h • x ∈ F '' P ∧ h • y ∈ F '' P)
    (x y : Ω) : Γ.Adj x y ↔ Γ'.Adj (F x) (F y) := by
  constructor
  · intro hxy
    obtain ⟨h, hxP, hyP⟩ := hcov x y hxy
    have hadj := hP (h • x) hxP (h • y) hyP
    have h' := hadj.mp (hΓ h x y hxy)
    rw [hF h x, hF h y] at h'
    have := hΓ' (θ h)⁻¹ (θ h • F x) (θ h • F y) h'
    simpa using this
  · intro hxy
    obtain ⟨h', hxP, hyP⟩ := hcov' (F x) (F y) hxy
    let h : H := θ.symm h'
    have hh : h' = θ h := (θ.apply_symm_apply h').symm
    have hxF : F (h • x) ∈ F '' P := by
      simpa [hF h x, ← hh] using hxP
    have hyF : F (h • y) ∈ F '' P := by
      simpa [hF h y, ← hh] using hyP
    obtain ⟨px, hpxP, hpx⟩ := (Set.mem_image F P (F (h • x))).mp hxF
    obtain ⟨py, hpyP, hpy⟩ := (Set.mem_image F P (F (h • y))).mp hyF
    have hxP : h • x ∈ P := by
      have hpx' : px = h • x := F.injective hpx
      rwa [hpx'] at hpxP
    have hyP : h • y ∈ P := by
      have hpy' : py = h • y := F.injective hpy
      rwa [hpy'] at hpyP
    have hPadj := hP (h • x) hxP (h • y) hyP
    have hΓxy : Γ.Adj (h • x) (h • y) := by
      apply hPadj.mpr
      rw [hF h x, hF h y, ← hh]
      exact hΓ' h' (F x) (F y) hxy
    have := hΓ h⁻¹ (h • x) (h • y) hΓxy
    simpa using this

end CFSG.GroupTheory

end
