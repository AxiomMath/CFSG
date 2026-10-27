module

public import CFSG.LocalAnalysis.GL83PartI.I_24_3.GenAux

public section

namespace GL83.I243

open Subgroup

namespace Gen

variable {X : Type*} [Group X]

abbrev commGroupOfCommute (Z : Subgroup X) (h : ∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a) :
    CommGroup Z :=
  { (inferInstance : Group Z) with mul_comm := fun a b => Subtype.ext (h a a.2 b b.2) }

theorem conj_mem_centralizer {K : Subgroup X} {f c : X} (hfN : f ∈ normalizer (K : Set X))
    (hc : c ∈ centralizer (K : Set X)) : f * c * f⁻¹ ∈ centralizer (K : Set X) := by
  rw [mem_centralizer_iff]
  intro h hh
  have hh' : f⁻¹ * h * f ∈ K := by
    have := (mem_normalizer_iff.1 (inv_mem hfN) h).1 hh
    simpa using this
  have h1 := mem_centralizer_iff.1 hc _ hh'
  calc h * (f * c * f⁻¹) = f * ((f⁻¹ * h * f) * c) * f⁻¹ := by group
    _ = f * (c * (f⁻¹ * h * f)) * f⁻¹ := by rw [h1]
    _ = f * c * f⁻¹ * h := by group

theorem mem_normalizer_sup_zpowers [Finite X] {g f z : X}
    (hf : g⁻¹ * f * g ∈ zpowers f ⊔ zpowers z) (hz : g⁻¹ * z * g ∈ zpowers f ⊔ zpowers z) :
    g ∈ normalizer ((zpowers f ⊔ zpowers z : Subgroup X) : Set X) := by
  set Q : Subgroup X := zpowers f ⊔ zpowers z with hQ
  have hle : Q ≤ Q.comap (MulAut.conj g⁻¹).toMonoidHom := by
    refine sup_le (zpowers_le.2 ?_) (zpowers_le.2 ?_)
    · simpa [MulAut.conj_apply] using hf
    · simpa [MulAut.conj_apply] using hz
  have hinv : g⁻¹ ∈ normalizer (Q : Set X) := by
    refine mem_normalizer_fintype fun n hn => ?_
    simpa [MulAut.conj_apply] using hle hn
  simpa using inv_mem hinv

end Gen

theorem exists_central_mul_mem_normalizer
    {X : Type*} [Group X] [Finite X]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {K : Subgroup X} {f z k : X}
    (hfN : f ∈ Subgroup.normalizer (K : Set X)) (hfp : f ^ p = 1)
    (hzK : z ∈ K) (hzc : z ∈ Subgroup.centralizer (K : Set X)) (hzp : orderOf z = p)
    (hfz : f * z = z * f)
    (hΩ : ∀ c ∈ K, c ∈ Subgroup.centralizer (K : Set X) → c ^ p = 1 → c ∈ Subgroup.zpowers z)
    (hk : k ∈ K) (hζ : f * k * f⁻¹ * k⁻¹ ∈ Subgroup.centralizer (K : Set X)) :
    ∃ c ∈ K, c ∈ Subgroup.centralizer (K : Set X) ∧
      k * c ∈ Subgroup.normalizer
        ((Subgroup.zpowers f ⊔ Subgroup.zpowers z : Subgroup X) : Set X) := by
  clear hfz
  obtain ⟨Z, hZ⟩ : ∃ Z : Subgroup X, Z = K ⊓ centralizer (K : Set X) := ⟨_, rfl⟩
  have hZmem : ∀ x, x ∈ Z ↔ x ∈ K ∧ x ∈ centralizer (K : Set X) := fun x => by
    rw [hZ]
    exact Iff.rfl
  have hZcomm : ∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a := fun a ha b hb =>
    mem_centralizer_iff.1 ((hZmem b).1 hb).2 a ((hZmem a).1 ha).1
  have hfZ : ∀ c ∈ Z, f * c * f⁻¹ ∈ Z := fun c hc => by
    rw [hZmem] at hc ⊢
    exact ⟨(mem_normalizer_iff.1 hfN c).1 hc.1, Gen.conj_mem_centralizer hfN hc.2⟩
  letI : CommGroup Z := Gen.commGroupOfCommute Z hZcomm
  obtain ⟨t, ht_apply⟩ : ∃ t : Monoid.End Z, ∀ c : Z, ((t c : Z) : X) = f * c * f⁻¹ := by
    let t₀ : Z →* Z :=
      { toFun := fun c => ⟨f * c * f⁻¹, hfZ c c.2⟩
        map_one' := Subtype.ext (by simp)
        map_mul' := fun a b => Subtype.ext (by simp [mul_assoc]) }
    exact ⟨t₀, fun c => rfl⟩
  have hti : ∀ (i : ℕ) (c : Z), (((t ^ i) c : Z) : X) = f ^ i * c * (f ^ i)⁻¹ := by
    intro i
    induction i with
    | zero => intro c; simp
    | succ i ih =>
      intro c
      rw [pow_succ']
      show (((t ((t ^ i) c) : Z)) : X) = _
      rw [ht_apply, ih]
      group
  have htp : t ^ p = 1 := by
    refine DFunLike.ext _ _ fun c => Subtype.ext ?_
    rw [hti, hfp]
    simp
  have hζZ : f * k * f⁻¹ * k⁻¹ ∈ Z :=
    (hZmem _).2 ⟨K.mul_mem ((mem_normalizer_iff.1 hfN k).1 hk) (K.inv_mem hk), hζ⟩
  obtain ⟨ζ, hζdef⟩ : ∃ ζ : Z, (ζ : X) = f * k * f⁻¹ * k⁻¹ := ⟨⟨_, hζZ⟩, rfl⟩
  obtain ⟨z', hz'⟩ : ∃ z' : Z, (z' : X) = z := ⟨⟨z, (hZmem z).2 ⟨hzK, hzc⟩⟩, rfl⟩
  have hz'p : orderOf z' = p := by
    rw [← hzp, ← hz']
    exact (Subgroup.orderOf_coe z').symm
  have hΩ' : ∀ c : Z, c ^ p = 1 → c ∈ zpowers z' := by
    intro c hc
    have hcX : (c : X) ^ p = 1 := by
      have := congrArg (fun w : Z => (w : X)) hc
      simpa using this
    obtain ⟨h1, h2⟩ := (hZmem c).1 c.2
    obtain ⟨n, hn⟩ := mem_zpowers_iff.1 (hΩ c h1 h2 hcX)
    refine mem_zpowers_iff.2 ⟨n, Subtype.ext ?_⟩
    rw [Subgroup.coe_zpow, hz']
    exact hn
  have hkζ : k * (ζ : X) = ζ * k := mem_centralizer_iff.1 (by rwa [hζdef]) k hk
  have hkf : k⁻¹ * f * k = (ζ : X) * f := by
    calc k⁻¹ * f * k = k⁻¹ * (ζ : X) * k * f := by rw [hζdef]; group
      _ = (ζ : X) * f := by rw [mul_assoc k⁻¹, ← hkζ, inv_mul_cancel_left]
  have hprod : ∀ n : ℕ, ((ζ : X) * f) ^ n
      = ((∏ i ∈ Finset.range n, (t ^ i) ζ : Z) : X) * f ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, ih, Finset.prod_range_succ, Subgroup.coe_mul, hti, pow_succ]
      group
  have hN : ∏ i ∈ Finset.range p, (t ^ i) ζ = 1 := by
    refine Subtype.ext ?_
    have h1 : (k⁻¹ * f * k) ^ p = 1 := by
      have := conj_pow (a := k⁻¹) (b := f) (i := p)
      simp only [inv_inv] at this
      rw [this, hfp]
      simp
    rw [hkf, hprod p, hfp, mul_one] at h1
    exact h1
  obtain ⟨c, hc⟩ := Gen.exists_mul_inv_map_mem_zpowers hp hp2 htp hz'p hΩ' hN
  obtain ⟨s, hs⟩ := mem_zpowers_iff.1 hc
  have hs' : z ^ s = (ζ : X) * ((c : X)⁻¹ * (f * c * f⁻¹)) := by
    have := congrArg (fun w : Z => (w : X)) hs
    simpa [ht_apply, hz'] using this
  have hcomm : (c : X)⁻¹ * ζ = ζ * (c : X)⁻¹ :=
    hZcomm _ (Z.inv_mem c.2) _ ζ.2
  have hconjf : (k * c)⁻¹ * f * (k * c) = z ^ s * f := by
    calc (k * c)⁻¹ * f * (k * c) = (c : X)⁻¹ * (k⁻¹ * f * k) * c := by group
      _ = (c : X)⁻¹ * ((ζ : X) * f) * c := by rw [hkf]
      _ = ((c : X)⁻¹ * ζ) * (f * c * f⁻¹) * f := by group
      _ = (ζ * (c : X)⁻¹) * (f * c * f⁻¹) * f := by rw [hcomm]
      _ = (ζ : X) * ((c : X)⁻¹ * (f * c * f⁻¹)) * f := by group
      _ = z ^ s * f := by rw [hs']
  have hcK : (c : X) ∈ K := ((hZmem c).1 c.2).1
  have hcC : (c : X) ∈ centralizer (K : Set X) := ((hZmem c).1 c.2).2
  have hkz : k * z = z * k := mem_centralizer_iff.1 hzc k hk
  have hcz : (c : X) * z = z * c := mem_centralizer_iff.1 hzc c hcK
  have hconjz : (k * c)⁻¹ * z * (k * c) = z := by
    calc (k * c)⁻¹ * z * (k * c) = (c : X)⁻¹ * (k⁻¹ * z * k) * c := by group
      _ = (c : X)⁻¹ * z * c := by rw [mul_assoc k⁻¹, ← hkz, inv_mul_cancel_left]
      _ = z := by rw [mul_assoc, ← hcz, inv_mul_cancel_left]
  refine ⟨c, hcK, hcC, Gen.mem_normalizer_sup_zpowers ?_ ?_⟩
  · rw [hconjf]
    exact Subgroup.mul_mem _ (Subgroup.zpow_mem _ (mem_sup_right (mem_zpowers z)) s)
      (mem_sup_left (mem_zpowers f))
  · rw [hconjz]
    exact mem_sup_right (mem_zpowers z)

end GL83.I243
