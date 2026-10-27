module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabCommOrthMinusDefs
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabCommOrthMinusPlane

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm.OrthMinus

open Module QuadraticMap Matrix CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.Classical2
  CFSG.RankThree.PartOne.KCOrthogonal CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit CFSG.AGLEmbedding.LeviBlock
open scoped commutatorElement

variable {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K} {r s : ℕ} {d : Fin (s + 1) → ℕ}

local notation "𝕍" => (Fin r ⊕ Fin r → K) × (Fin 2 → K)

section Conj

@[expose] def IsConjBy
    (α : MulAut ↥(orthElementaryGroup (quadTail r (minusTailForm K b c)))) (f : 𝕍 ≃ₗ[K] 𝕍) :
    Prop :=
  ∀ g : ↥(orthElementaryGroup (quadTail r (minusTailForm K b c))),
    ((α g : ↥(orthElementaryGroup (quadTail r (minusTailForm K b c)))) : 𝕍 ≃ₗ[K] 𝕍) =
      f * (g : 𝕍 ≃ₗ[K] 𝕍) * f⁻¹

variable {α β : MulAut ↥(orthElementaryGroup (quadTail r (minusTailForm K b c)))}
  {f f' : ((Fin r ⊕ Fin r → K) × (Fin 2 → K)) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × (Fin 2 → K))}

theorem IsConjBy.mul (hα : IsConjBy α f) (hβ : IsConjBy β f') : IsConjBy (α * β) (f * f') := by
  intro g
  rw [MulAut.mul_apply, hα, hβ]
  group

theorem IsConjBy.inv (hα : IsConjBy α f) : IsConjBy α⁻¹ f⁻¹ := by
  intro g
  have h := hα (α⁻¹ g)
  rw [MulAut.apply_inv_self] at h
  rw [inv_inv, h]
  group

theorem IsConjBy.one : IsConjBy (1 : MulAut ↥(orthElementaryGroup (quadTail r
    (minusTailForm K b c)))) (1 : 𝕍 ≃ₗ[K] 𝕍) := by
  intro g
  simp

theorem IsConjBy.pow (hα : IsConjBy α f) (n : ℕ) : IsConjBy (α ^ n) (f ^ n) := by
  induction n with
  | zero => simpa using IsConjBy.one
  | succ n ih => rw [pow_succ, pow_succ]; exact ih.mul hα

theorem IsConjBy.commutator (hα : IsConjBy α f) (hβ : IsConjBy β f') :
    IsConjBy ⁅α, β⁆ ⁅f, f'⁆ := by
  rw [commutatorElement_def, commutatorElement_def]
  exact ((hα.mul hβ).mul hα.inv).mul hβ.inv

theorem IsConjBy.pow_eq_one (hα : IsConjBy α f) {n : ℕ} (hf : f ^ n = 1) : α ^ n = 1 := by
  refine MulEquiv.ext fun g => Subtype.ext ?_
  rw [(hα.pow n) g, hf]
  simp

theorem IsConjBy.pow_commute (hα : IsConjBy α f) {n : ℕ} (hn : α ^ n = 1)
    (g : ↥(orthElementaryGroup (quadTail r (minusTailForm K b c)))) :
    (f ^ n) * (g : 𝕍 ≃ₗ[K] 𝕍) = (g : 𝕍 ≃ₗ[K] 𝕍) * (f ^ n) := by
  have h := (hα.pow n) g
  rw [hn] at h
  have h' : (g : 𝕍 ≃ₗ[K] 𝕍) = f ^ n * (g : 𝕍 ≃ₗ[K] 𝕍) * (f ^ n)⁻¹ := h
  calc f ^ n * (g : 𝕍 ≃ₗ[K] 𝕍) = (f ^ n * (g : 𝕍 ≃ₗ[K] 𝕍) * (f ^ n)⁻¹) * f ^ n := by group
    _ = (g : 𝕍 ≃ₗ[K] 𝕍) * f ^ n := by rw [← h']

end Conj

section Data

@[expose] def SemiData.toLinear (S : SemiData K r b c) (hσ : ∀ a : K, S.σ a = a) : 𝕍 ≃ₗ[K] 𝕍 where
  toFun := S.F
  map_add' := S.F.map_add
  map_smul' := fun a v => by rw [S.hF, hσ, RingHom.id_apply]
  invFun := S.F.symm
  left_inv := S.F.left_inv
  right_inv := S.F.right_inv

theorem SemiData.toLinear_apply (S : SemiData K r b c) (hσ : ∀ a : K, S.σ a = a) (v : 𝕍) :
    S.toLinear hσ v = S.F v := rfl

theorem SemiData.isConjBy {S : SemiData K r b c}
    {α : MulAut ↥(orthElementaryGroup (quadTail r (minusTailForm K b c)))} (hS : S.Induces α)
    (hσ : ∀ a : K, S.σ a = a) : IsConjBy α (S.toLinear hσ) := by
  intro g
  unfold SemiData.Induces at hS
  rw [hS g]
  refine LinearEquiv.ext fun v => ?_
  rfl

@[expose] def perpSub {t : ℕ} (ht : t ≤ r) : Submodule K 𝕍 where
  carrier := {v | IsResPerp ht v}
  add_mem' := fun {a b} ha hb i => by
    have := ha i
    have := hb i
    simp [*]
  zero_mem' := fun i => rfl
  smul_mem' := fun a v hv i => by
    have := hv i
    simp [*]

theorem mem_perpSub {t : ℕ} {ht : t ≤ r} {v : 𝕍} :
    v ∈ perpSub (K := K) (r := r) ht ↔ IsResPerp ht v :=
  Iff.rfl

end Data

section ExistsData

theorem phiB_scalar_ne_zero (hd : OrthCuts r d) (S : SemiData K r b c)
    (hflag : ∀ (i : Fin (s + 1)) (v : (Fin r ⊕ Fin r → K) × (Fin 2 → K)),
      S.F v ∈ tailFlag K (Fin 2 → K) r (d i) ↔ v ∈ tailFlag K (Fin 2 → K) r (d i))
    (l : Fin s) {a : K} (ha : ∀ u, phiB hd S l u = a • u) : a ≠ 0 := by
  have hpos : 0 < d l.succ - d l.castSucc := by
    have := hd.mono (Fin.castSucc_lt_succ (i := l))
    omega
  intro h0
  let i₀ : Fin (d l.succ - d l.castSucc) := ⟨0, hpos⟩
  have h1 : phiB hd S l (Pi.single i₀ 1) = phiB hd S l 0 := by
    rw [ha, ha, h0, zero_smul, zero_smul]
  have h2 := phiB_injective hd S hflag l h1
  have := congrFun h2 i₀
  simp at this

theorem exists_data (hr : 3 ≤ r) (hirr : ∀ t : K, t ^ 2 + b * t + c ≠ 0) (hd : OrthCuts r d)
    (hbig : (∃ l : Fin s, 2 ≤ d l.succ - d l.castSucc) ∨ 1 ≤ r - d (Fin.last s))
    {α : MulAut ↥(orthElementaryGroup (quadTail r (minusTailForm K b c)))}
    (hodd : Odd (orderOf α)) (hn : OmNormFix hr hirr hd α) :
    ∃ (Fl : 𝕍 ≃ₗ[K] 𝕍) (μ : K), μ ≠ 0 ∧ IsConjBy α Fl ∧
      (∀ v, quadTail r (minusTailForm K b c) (Fl v) =
        μ * quadTail r (minusTailForm K b c) v) ∧
      (∀ (i : Fin (s + 1)) (v : 𝕍), Fl v ∈ tailFlag K (Fin 2 → K) r (d i) ↔
        v ∈ tailFlag K (Fin 2 → K) r (d i)) ∧
      (∀ v : 𝕍, IsResPerp hd.last (Fl v) ↔ IsResPerp hd.last v) ∧
      (∀ l : Fin s, ∃ a : K, a ≠ 0 ∧ ScalarMod (tailFlag K (Fin 2 → K) r (d l.succ))
        (tailFlag K (Fin 2 → K) r (d l.castSucc)) Fl a) ∧
      (1 ≤ r - d (Fin.last s) → ∃ a : K, a ≠ 0 ∧ ScalarMod (perpSub (K := K) (r := r) hd.last)
        (tailFlag K (Fin 2 → K) r (d (Fin.last s))) Fl a) ∧
      ∃ (N : ℕ) (a : K), Odd N ∧ ∀ v, (Fl ^ N) v = a • v := by
  classical
  haveI : Finite (𝕍 ≃ₗ[K] 𝕍) := finite_orthLinearEquiv
  obtain ⟨S, hS⟩ := exists_semiData hr hirr α
  have hnorm : ∀ u ∈ orthParab r (minusTailForm K b c) d,
      ∃ x ∈ orthParab r (minusTailForm K b c) d, ∀ v,
        ((u : ↥(orthElementaryGroup (quadTail r (minusTailForm K b c)))) : 𝕍 ≃ₗ[K] 𝕍) v =
          S.F (((x : ↥(orthElementaryGroup (quadTail r (minusTailForm K b c)))) : 𝕍 ≃ₗ[K] 𝕍)
            (S.F.symm v)) := by
    intro u hu
    let φ : ↥(orthParab r (minusTailForm K b c) d) → ↥(orthParab r (minusTailForm K b c) d) :=
      fun x => ⟨α x, hn.1 x x.2⟩
    have hinj : Function.Injective φ := fun x y h =>
      Subtype.ext (α.injective (congrArg Subtype.val h))
    obtain ⟨x, hx⟩ := Finite.injective_iff_surjective.1 hinj ⟨u, hu⟩
    refine ⟨x, x.2, fun v => ?_⟩
    have h1 : α (x : ↥(orthElementaryGroup (quadTail r (minusTailForm K b c)))) = u :=
      congrArg Subtype.val hx
    have h2 := hS (x : ↥(orthElementaryGroup (quadTail r (minusTailForm K b c))))
    rw [h1] at h2
    rw [h2]
    rfl
  have hflag := mem_flag_iff_of_normalizes hirr hd S.hF S.hFQ hnorm
  have hrel : ∀ (l : Fin s) (B : SpecialLinearGroup (Fin (d l.succ - d l.castSucc)) K)
      (u : Fin (d l.succ - d l.castSucc) → K),
      phiB hd S l ((B : Matrix _ _ K) *ᵥ u) = (B : Matrix _ _ K) *ᵥ phiB hd S l u := by
    intro l B u
    obtain ⟨u₀, hu₀, hu₀e⟩ := hn.2.1 l B
    set x := orthLeviSL hd (minusTailForm K b c) hr l B with hx
    have hxy : orthBlockMat hd l (((u₀ * x : ↥(orthParab r (minusTailForm K b c) d)) :
        ↥(orthElementaryGroup (quadTail r (minusTailForm K b c)))) : 𝕍 ≃ₗ[K] 𝕍) =
        orthBlockMat hd l ((x : ↥(orthElementaryGroup (quadTail r (minusTailForm K b c)))) :
          𝕍 ≃ₗ[K] 𝕍) := by
      have h1 : orthBlockHom (minusTailForm K b c) hd l (u₀ * x) =
          orthBlockHom (minusTailForm K b c) hd l x := by rw [map_mul, hu₀, one_mul]
      have h2 := congrArg (fun z : GL (Fin (d l.succ - d l.castSucc)) K =>
        (z : Matrix (Fin (d l.succ - d l.castSucc)) (Fin (d l.succ - d l.castSucc)) K)) h1
      simpa only [coe_orthBlockHom] using h2
    have hconj : ∀ v, (((u₀ * x : ↥(orthParab r (minusTailForm K b c) d)) :
        ↥(orthElementaryGroup (quadTail r (minusTailForm K b c)))) : 𝕍 ≃ₗ[K] 𝕍) v =
        S.F (((x : ↥(orthElementaryGroup (quadTail r (minusTailForm K b c)))) : 𝕍 ≃ₗ[K] 𝕍)
          (S.F.symm v)) := by
      intro v
      have h1 : ((u₀ * x : ↥(orthParab r (minusTailForm K b c) d)) :
          ↥(orthElementaryGroup (quadTail r (minusTailForm K b c)))) =
          α (x : ↥(orthElementaryGroup (quadTail r (minusTailForm K b c)))) := by
        rw [Subgroup.coe_mul, hu₀e, inv_mul_cancel_right]
      rw [h1]
      have h2 := hS (x : ↥(orthElementaryGroup (quadTail r (minusTailForm K b c))))
      rw [h2]
      rfl
    have h := phiB_comm hd S hflag l x (u₀ * x) hxy hconj u
    have hMx : orthBlockMat hd l ((x : ↥(orthElementaryGroup (quadTail r
        (minusTailForm K b c)))) : 𝕍 ≃ₗ[K] 𝕍) = (B : Matrix _ _ K) := by
      have := congrArg (fun z : GL (Fin (d l.succ - d l.castSucc)) K =>
        (z : Matrix (Fin (d l.succ - d l.castSucc)) (Fin (d l.succ - d l.castSucc)) K))
        (orthBlockHom_orthLeviSL_self hd (minusTailForm K b c) hr l B)
      simp only [coe_orthBlockHom] at this
      exact this
    rwa [hMx] at h
  have hresrel : 1 ≤ r - d (Fin.last s) →
      ∀ g ∈ orthDerived (quadTail (r - d (Fin.last s)) (minusTailForm K b c)),
        ∀ u, resFun S hd.last (g u) = g (resFun S hd.last u) := by
    intro hm g hg u
    obtain ⟨u₀, hu₀, hu₀e⟩ := hn.2.2 hm g hg
    set x := orthLeviResElt b c hd (commutator_orthogonalGroup_quadTail_minus hr hirr)
      ⟨g, hg⟩ with hx
    have hxe : ((x : ↥(orthElementaryGroup (quadTail r (minusTailForm K b c)))) :
        𝕍 ≃ₗ[K] 𝕍) = orthLeviRes K (Fin 2 → K) hd.last g := rfl
    have hy : orthResHom (minusTailForm K b c) hd (u₀ * x) = g := by
      rw [map_mul, hu₀, one_mul]
      exact orthResHom_orthLeviResElt hd _ ⟨g, hg⟩
    have hconj : ∀ v, (((u₀ * x : ↥(orthParab r (minusTailForm K b c) d)) :
        ↥(orthElementaryGroup (quadTail r (minusTailForm K b c)))) : 𝕍 ≃ₗ[K] 𝕍) v =
        S.F (((x : ↥(orthElementaryGroup (quadTail r (minusTailForm K b c)))) : 𝕍 ≃ₗ[K] 𝕍)
          (S.F.symm v)) := by
      intro v
      have h1 : ((u₀ * x : ↥(orthParab r (minusTailForm K b c) d)) :
          ↥(orthElementaryGroup (quadTail r (minusTailForm K b c)))) =
          α (x : ↥(orthElementaryGroup (quadTail r (minusTailForm K b c)))) := by
        rw [Subgroup.coe_mul, hu₀e, inv_mul_cancel_right]
      rw [h1]
      have h2 := hS (x : ↥(orthElementaryGroup (quadTail r (minusTailForm K b c))))
      rw [h2]
      rfl
    exact resFun_comm S hd (fun v => hflag (Fin.last s) v) g x (u₀ * x) hxe hy hconj u
  have hflagL : ∀ v : 𝕍, S.F v ∈ tailFlag K (Fin 2 → K) r (d (Fin.last s)) ↔
      v ∈ tailFlag K (Fin 2 → K) r (d (Fin.last s)) := fun v => hflag (Fin.last s) v
  have hσ : ∀ a : K, S.σ a = a := by
    rcases hbig with ⟨l, hl⟩ | hm
    · exact (block_sigma_and_scalar hd S hflag l hl (hrel l)).1
    · exact (res_sigma_and_scalar S hd hflagL hirr hm (hresrel hm)).1
  have hconj : IsConjBy α (S.toLinear hσ) := SemiData.isConjBy hS hσ
  have hquad : ∀ v, quadTail r (minusTailForm K b c) (S.toLinear hσ v) =
      S.μ * quadTail r (minusTailForm K b c) v := fun v => by
    rw [SemiData.toLinear_apply, S.hFQ, hσ]
  have hperp : ∀ v : 𝕍, IsResPerp hd.last (S.toLinear hσ v) ↔ IsResPerp hd.last v :=
    isResPerp_iff S hd.last hflagL
  have hblk : ∀ l : Fin s, ∃ a : K, a ≠ 0 ∧ ScalarMod (tailFlag K (Fin 2 → K) r (d l.succ))
      (tailFlag K (Fin 2 → K) r (d l.castSucc)) (S.toLinear hσ) a := by
    intro l
    by_cases hk : 2 ≤ d l.succ - d l.castSucc
    · obtain ⟨-, a, ha0, ha⟩ := block_sigma_and_scalar hd S hflag l hk (hrel l)
      exact ⟨a, ha0, scalarMod_of_phiB hd S hflag l ha⟩
    · obtain ⟨a, ha⟩ := phiB_scalar_of_le_one hd S hσ l (by omega)
      exact ⟨a, phiB_scalar_ne_zero hd S hflag l ha, scalarMod_of_phiB hd S hflag l ha⟩
  have hres1 : 1 ≤ r - d (Fin.last s) → ∃ a : K, a ≠ 0 ∧
      ScalarMod (perpSub (K := K) (r := r) hd.last)
        (tailFlag K (Fin 2 → K) r (d (Fin.last s))) (S.toLinear hσ) a := by
    intro hm
    obtain ⟨-, a, ha0, ha⟩ := res_sigma_and_scalar S hd hflagL hirr hm (hresrel hm)
    exact ⟨a, ha0, fun v hv => scalarMod_res S hd hflagL ha (mem_perpSub.1 hv)⟩
  obtain ⟨N, hNodd, hN1⟩ : ∃ N : ℕ, Odd N ∧ α ^ N = 1 := ⟨orderOf α, hodd, pow_orderOf_eq_one α⟩
  have hE : orthDerived (quadTail r (minusTailForm K b c)) =
      orthElementaryGroup (quadTail r (minusTailForm K b c)) :=
    commutator_orthogonalGroup_quadTail_minus hr hirr
  have hpowcomm : ∀ g ∈ orthDerived (quadTail r (minusTailForm K b c)), ∀ v,
      ((S.toLinear hσ) ^ N) (g v) = g (((S.toLinear hσ) ^ N) v) := by
    intro g hg v
    have hgE : g ∈ orthElementaryGroup (quadTail r (minusTailForm K b c)) := by
      rw [← hE]
      exact hg
    have := hconj.pow_commute hN1 ⟨g, hgE⟩
    exact LinearEquiv.congr_fun this v
  have hGQ : ∀ (n : ℕ) (v : 𝕍), quadTail r (minusTailForm K b c) (((S.toLinear hσ) ^ n) v) =
      S.μ ^ n * quadTail r (minusTailForm K b c) v := by
    intro n
    induction n with
    | zero => intro v; simp
    | succ n ih =>
      intro v
      rw [pow_succ, LinearEquiv.mul_apply, ih, hquad, pow_succ]
      ring
  obtain ⟨-, a, -, ha⟩ := schur_tail (m := r) (by omega) hirr (((S.toLinear hσ) ^ N).toAddEquiv)
    (RingEquiv.refl K) (fun a v => by simp) (S.μ ^ N) (fun v => by simpa using hGQ N v)
    (fun g hg v => hpowcomm g hg v)
  exact ⟨S.toLinear hσ, S.μ, S.hμ, hconj, hquad, hflag, hperp, hblk, hres1, N, a, hNodd,
    fun v => ha v⟩

end ExistsData

section Model

theorem isSim_of_quad {g : 𝕍 ≃ₗ[K] 𝕍} {μ : K}
    (hq : ∀ v, quadTail r (minusTailForm K b c) (g v) =
      μ * quadTail r (minusTailForm K b c) v) : IsSim (b := b) (c := c) g μ := by
  intro x y
  show quadTail r (minusTailForm K b c) (g x + g y) - quadTail r (minusTailForm K b c) (g x) -
    quadTail r (minusTailForm K b c) (g y) = μ * (quadTail r (minusTailForm K b c) (x + y) -
      quadTail r (minusTailForm K b c) x - quadTail r (minusTailForm K b c) y)
  rw [← map_add g, hq, hq, hq]
  ring

theorem om_model_comm (hr : 3 ≤ r) (hirr : ∀ t : K, t ^ 2 + b * t + c ≠ 0) (hd : OrthCuts r d)
    (hbig : (∃ l : Fin s, 2 ≤ d l.succ - d l.castSucc) ∨ 1 ≤ r - d (Fin.last s))
    {α₁ α₂ : MulAut ↥(orthElementaryGroup (quadTail r (minusTailForm K b c)))}
    (h₁ : Odd (orderOf α₁)) (h₂ : Odd (orderOf α₂)) (h₁₂ : Odd (orderOf ⁅α₁, α₂⁆))
    (hn₁ : OmNormFix hr hirr hd α₁) (hn₂ : OmNormFix hr hirr hd α₂) : ⁅α₁, α₂⁆ = 1 := by
  obtain ⟨Fl₁, μ₁, hμ₁, hc₁, hq₁, hf₁, hp₁, hb₁, hr₁, N₁, a₁, hN₁, hs₁⟩ :=
    exists_data hr hirr hd hbig h₁ hn₁
  obtain ⟨Fl₂, μ₂, hμ₂, hc₂, hq₂, hf₂, hp₂, hb₂, hr₂, N₂, a₂, hN₂, hs₂⟩ :=
    exists_data hr hirr hd hbig h₂ hn₂
  have hres : ∀ v : 𝕍, IsResPerp hd.last v →
      (⁅Fl₁, Fl₂⁆ : 𝕍 ≃ₗ[K] 𝕍) v - v ∈ tailFlag K (Fin 2 → K) r (d (Fin.last s)) := by
    by_cases hm : 1 ≤ r - d (Fin.last s)
    · obtain ⟨e₁, he₁, hse₁⟩ := hr₁ hm
      obtain ⟨e₂, he₂, hse₂⟩ := hr₂ hm
      have hsymm : ∀ (g : 𝕍 ≃ₗ[K] 𝕍) (T : Submodule K 𝕍), (∀ v, g v ∈ T ↔ v ∈ T) →
          ∀ w ∈ T, g.symm w ∈ T := fun g T hg w hw =>
        (hg _).1 (by rwa [LinearEquiv.apply_symm_apply])
      have hperpT : ∀ (g : 𝕍 ≃ₗ[K] 𝕍), (∀ v : 𝕍, IsResPerp hd.last (g v) ↔ IsResPerp hd.last v) →
          ∀ w ∈ perpSub (K := K) (r := r) hd.last, g.symm w ∈ perpSub (K := K) (r := r) hd.last :=
        fun g hg w hw => (hg (g.symm w)).1 (by
          have : g (g.symm w) = w := LinearEquiv.apply_symm_apply g w
          rw [this]
          exact mem_perpSub.1 hw)
      have := ScalarMod.commutator hse₁ hse₂ he₁ he₂ (fun w hw => (hf₁ _ w).2 hw)
        (fun w hw => (hf₂ _ w).2 hw) (hsymm Fl₁ _ (hf₁ _)) (hperpT Fl₁ hp₁) (hperpT Fl₂ hp₂)
      intro v hv
      have h := this v (mem_perpSub.2 hv)
      rwa [one_smul] at h
    · have hm0 : r - d (Fin.last s) = 0 := by omega
      exact commutator_sub_mem_of_plane hd.last hm0 hirr
        (mem_G0 hd.last |>.2 ⟨fun v => hf₁ (Fin.last s) v, hp₁⟩)
        (mem_G0 hd.last |>.2 ⟨fun v => hf₂ (Fin.last s) v, hp₂⟩) hq₁ hq₂ hN₁ hN₂ hs₁ hs₂
  have hpow := commutator_pow_eq_one hd hμ₁ hμ₂ (isSim_of_quad hq₁) (isSim_of_quad hq₂) hf₁ hf₂
    hb₁ hb₂ hres
  have hp := (hc₁.commutator hc₂).pow_eq_one hpow
  have hdvd : orderOf ⁅α₁, α₂⁆ ∣ 2 ^ (2 * s + 1) := orderOf_dvd_of_pow_eq_one hp
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  have hj0 : j = 0 := by
    by_contra hne
    rw [hj] at h₁₂
    exact (Nat.not_even_iff_odd.mpr h₁₂) (Nat.even_pow.mpr ⟨even_two, hne⟩)
  rw [hj0, pow_zero] at hj
  exact orderOf_eq_one_iff.mp hj

end Model

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm.OrthMinus
