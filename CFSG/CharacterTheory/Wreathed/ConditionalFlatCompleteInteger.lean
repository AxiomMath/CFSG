module

public import CFSG.CharacterTheory.Wreathed.ConditionalFlatCompleteNaming

public section

open scoped BigOperators Matrix

namespace CFSG.Wreathed.FlatComplete

open CFSG.Wreathed.ConditionalGeneralBase

@[expose] def CompleteSupport {I : Type*} [Fintype I] [DecidableEq I] (m M : ℕ) (d : I → ℤ)
    (X : ZMod m → I → ℤ) (Y : ℕ → I → ℤ) (c : ZMod m → ZMod m → I → ℤ)
    (V : Finset (ZMod m × ZMod m)) : Prop :=
  ∃ (δ₀ δ₁ δ₂ δ₃ δ₄ α β γ : ℤ) (χ₀ χ₁ χ₂ χ₃ χ₄ : I) (ξ : ℕ → I) (P Q : ℕ → Fin 2 → I)
    (ψ : ZMod m × ZMod m → I) (D Δ : ℤ),
    let Acol : I → ℤ := Pi.single χ₀ δ₀ + Pi.single χ₁ δ₁ + Pi.single χ₂ δ₂ + Pi.single χ₃ δ₃
    let Kc : I → ℤ := Pi.single χ₀ δ₀ - Pi.single χ₁ δ₁ + Pi.single χ₄ (2 * δ₄)
    let core : Finset I := {χ₀, χ₁, χ₂, χ₃, χ₄}
    let evenFam : Finset I :=
      ((Finset.Ico 1 M) ×ˢ (Finset.univ : Finset (Fin 2))).image (fun x => P x.1 x.2) ∪
        ((Finset.Ico 1 M) ×ˢ (Finset.univ : Finset (Fin 2))).image (fun x => Q x.1 x.2)
    (∀ s ∈ [δ₀, δ₁, δ₂, δ₃, δ₄, α, β, γ], s = 1 ∨ s = -1) ∧
    Function.Injective ![χ₀, χ₁, χ₂, χ₃, χ₄] ∧ Set.InjOn ξ (oddIdx m) ∧
    (∀ r ∈ Finset.Ico 1 M, ∀ r' ∈ Finset.Ico 1 M, ∀ e e' : Fin 2,
      (P r e = P r' e' → r = r' ∧ e = e') ∧ (Q r e = Q r' e' → r = r' ∧ e = e') ∧
        P r e ≠ Q r' e') ∧
    Set.InjOn ψ V ∧
    (∀ h ∈ oddIdx m, ξ h ∉ core) ∧
    (∀ r ∈ Finset.Ico 1 M, ∀ e, P r e ∉ core ∧ Q r e ∉ core ∧ P r e ∉ (oddIdx m).image ξ ∧
      Q r e ∉ (oddIdx m).image ξ) ∧
    (∀ J ∈ V, ψ J ∉ core ∧ ψ J ∉ (oddIdx m).image ξ ∧ ψ J ∉ evenFam) ∧
    Finset.univ = core ∪ (oddIdx m).image ξ ∪ evenFam ∪ V.image ψ ∧
    Fintype.card I = (m ^ 2 + 12 * m + 8) / 6 ∧
    (∀ h ∈ oddIdx m, X h = Acol + Pi.single (ξ h) (2 * α)) ∧
    Y 0 = β • (Pi.single χ₀ δ₀ + Pi.single χ₁ δ₁ - Pi.single χ₂ δ₂ - Pi.single χ₃ δ₃) ∧
    c M M = Kc + Pi.single χ₂ δ₂ - Pi.single χ₃ δ₃ ∧
    (∀ r ∈ Finset.Ico 1 M, X (-(2 * (r : ZMod m))) = Acol - Pi.single (P r 0) δ₂ -
      Pi.single (P r 1) δ₂ - Pi.single (Q r 0) δ₃ - Pi.single (Q r 1) δ₃) ∧
    (∀ r ∈ Finset.Ico 1 M, Y r = -Pi.single (P r 0) δ₂ + Pi.single (P r 1) δ₂ -
      Pi.single (Q r 0) δ₃ + Pi.single (Q r 1) δ₃) ∧
    (∀ r ∈ Finset.Ico 1 M, ∃ e : Fin 2,
      c r r = Kc + Pi.single (P r e) δ₂ - Pi.single (Q r e) δ₃ ∧
      c (r + M) (r + M) = Kc + Pi.single (P r (1 - e)) δ₂ - Pi.single (Q r (1 - e)) δ₃) ∧
    (∀ J ∈ V, c J.1 J.2 = Kc + Pi.single (ψ J) γ) ∧
    0 < D ∧ 0 < Δ ∧ (∀ h ∈ oddIdx m, d (ξ h) = D) ∧
    (∀ r ∈ Finset.Ico 1 M, ∀ e, d (P r e) = d χ₂ ∧ d (Q r e) = d χ₃) ∧
    (∀ J ∈ V, d (ψ J) = Δ) ∧
    δ₀ * d χ₀ + δ₁ * d χ₁ = -(α * D) ∧ δ₂ * d χ₂ + δ₃ * d χ₃ = -(α * D) ∧
    δ₄ * d χ₄ = δ₃ * d χ₃ - δ₀ * d χ₀ ∧ δ₄ * d χ₄ = δ₁ * d χ₁ - δ₂ * d χ₂ ∧
    γ * Δ = δ₂ * d χ₂ - δ₃ * d χ₃ ∧ δ₂ * d χ₂ - δ₃ * d χ₃ ≠ 0

namespace ColumnData

variable {I : Type*} [Fintype I] [DecidableEq I] {m M : ℕ} [NeZero m] {d : I → ℤ}
  {X : ZMod m → I → ℤ} {Y : ℕ → I → ℤ} {c : ZMod m → ZMod m → I → ℤ}
  {V : Finset (ZMod m × ZMod m)} {Ys : I → ℤ}
  {i₀ i₁ i₂ i₃ i₄ : I} {p : oddIdx m → I} {q : Finset.Ico 1 M → Fin 4 → I}
  {δ₀ δ₁ δ₂ δ₃ δ₄ α : ℤ} {η : Finset.Ico 1 M → Fin 4 → ℤ} {D : ℤ}

theorem exists_mem_V (hD : ColumnData m M d X Y c V) : ∃ J, J ∈ V := by
  have hm := hD.hm
  have hM2 := hD.two_le_M
  have h1 : (1 : ZMod m) ≠ 0 := by
    have := natCast_ne_zero_of_lt (m := m) (j := 1) (by omega) (by omega)
    simpa using this
  have h2 : (2 : ZMod m) ≠ 0 := by
    have := natCast_ne_zero_of_lt (m := m) (j := 2) (by omega) (by omega)
    simpa using this
  have h6 : (MulAction.orbit (dualGroup m) ((0 : ZMod m), (1 : ZMod m))).ncard = 6 := by
    rw [ncard_orbit_eq_six_iff, nodup_dualSix_iff]
    refine ⟨fun h => h1 h.symm, fun h => h2 ?_, fun h => h1 ?_⟩
    · rw [neg_zero, zero_sub] at h
      linear_combination h
    · rw [neg_zero, zero_sub] at h
      linear_combination h
  obtain ⟨J, ⟨hJ, -⟩, -⟩ := hD.hVrep _ h6
  exact ⟨J, hJ⟩

theorem complete_of_B1 (hD : ColumnData m M d X Y c V)
    (G : FlatFrame m M d X Y c Ys i₀ i₁ i₂ i₃ i₄ p q δ₀ δ₁ δ₂ δ₃ δ₄ α η D) {s : ℤ}
    (hs : s = 1 ∨ s = -1) (hsY : Y 0 = s • Ys)
    (hB1 : ∀ k : Finset.Ico 1 M, CoreAt i₀ i₁ i₂ i₃ i₄ δ₀ δ₁ δ₂ δ₃ δ₄ 1 (c k.1 k.1)) :
    CompleteSupport m M d X Y c V := by
  have F := G.frame
  have hm := hD.hm
  have hM2 := hD.two_le_M
  have hd := hD.hd
  have hH := hD.two_le_card_oddIdx
  obtain ⟨h01, h02, h03, h04, h12, h13, h14, h23, h24, h34⟩ := F.core_ne
  choose a e σ σ' ξ x hσ hσ' hx hoff hpair hoff' hpair' using fun k => hD.diag_data G k
  have ha : ∀ k, a k = 1 := fun k => CoreAt.unique F.sδ₀ F.sδ₂ (hoff k).1 (hB1 k)
  have hx0 : ∀ k, x k = 0 := by
    intro k
    have h := hx k
    rw [ha k] at h
    exact mul_self_eq_zero.mp (by rw [h]; simp [caseNorm])
  have hoff1 : ∀ k, OffPairs i₀ i₁ i₂ i₃ i₄ δ₀ δ₁ δ₂ δ₃ δ₄ p q k (c k.1 k.1) 1 (ξ k) 0 := by
    intro k
    have h := hoff k
    rw [ha k, hx0 k] at h
    exact h
  have hoff1' : ∀ k, OffPairs i₀ i₁ i₂ i₃ i₄ δ₀ δ₁ δ₂ δ₃ δ₄ p q k (c (k.1 + M) (k.1 + M)) 1
      (ξ k) 0 := by
    intro k
    have h := hoff' k
    rw [ha k, hx0 k] at h
    exact h
  have hk₀ : 1 ∈ Finset.Ico 1 M := Finset.mem_Ico.mpr ⟨le_rfl, by omega⟩
  set k₀ : Finset.Ico 1 M := ⟨1, hk₀⟩ with hk₀def
  have hgen : ∀ J : ZMod m × ZMod m, ∃ (ψ : I) (γ : ℤ), J ∈ V →
      CoreAt i₀ i₁ i₂ i₃ i₄ δ₀ δ₁ δ₂ δ₃ δ₄ 1 (c J.1 J.2) ∧ (∀ h, c J.1 J.2 (p h) = 0) ∧
      (∀ k l, c J.1 J.2 (q k l) = 0) ∧ (γ = 1 ∨ γ = -1) ∧
      ψ ∈ outK i₀ i₁ i₂ i₃ i₄ p (q k₀) ∧ c J.1 J.2 ψ = γ ∧
      ∀ i ∈ outK i₀ i₁ i₂ i₃ i₄ p (q k₀), c J.1 J.2 i = if i = ψ then γ else 0 := by
    intro J
    by_cases hJ : J ∈ V
    · obtain ⟨oA, oYs, oE, oY⟩ := hD.frame_orth G.hYs J.1 J.2
      have hJC : c J.1 J.2 ⬝ᵥ c M M = 6 := by
        rw [dotProduct_comm]
        exact hD.hcrV _ hD.M_ne_zero J hJ
      have hJc : ∀ k : Finset.Ico 1 M, c J.1 J.2 ⬝ᵥ c k.1 k.1 = 6 := fun k => by
        rw [dotProduct_comm]
        exact hD.hcrV _ (hD.r_ne_zero k.2) J hJ
      have hJc' : ∀ k : Finset.Ico 1 M, c J.1 J.2 ⬝ᵥ c (k.1 + M) (k.1 + M) = 6 := fun k => by
        rw [dotProduct_comm]
        exact hD.hcrV _ (hD.rM_ne_zero k.2) J hJ
      have hk := fun k => F.generic_caseB hH k (hσ k) (hσ' k) (hoff1 k) (hpair k) (hoff1' k)
        (hpair' k) (hD.hcV J hJ) oA oYs hJC (oE k) (oY k) (hJc k) (hJc' k)
      obtain ⟨hcore, hp, -, ψ, γ, hγ, hψ, hψv, hval⟩ := hk k₀
      exact ⟨ψ, γ, fun _ => ⟨hcore, hp, fun k l => (hk k).2.2.1 l, hγ, hψ, hψv, hval⟩⟩
    · exact ⟨i₀, 1, fun h => absurd h hJ⟩
  choose ψ γ hgenJ using hgen
  have hγ0 : ∀ J ∈ V, γ J ≠ 0 := fun J hJ => by
    rcases (hgenJ J hJ).2.2.2.1 with h | h <;> rw [h] <;> norm_num
  have hψq : ∀ J ∈ V, ∀ k l, q k l ≠ ψ J := fun J hJ k l he => by
    obtain ⟨-, -, hq, -, -, hψv, -⟩ := hgenJ J hJ
    have h := hq k l
    rw [he, hψv] at h
    exact hγ0 J hJ h
  have hψc : ∀ J ∈ V, ψ J ∉ ({i₀, i₁, i₂, i₃, i₄} : Finset I) := fun J hJ =>
    (mem_outK.mp (hgenJ J hJ).2.2.2.2.1).1
  have hψp : ∀ J ∈ V, ∀ h, p h ≠ ψ J := fun J hJ =>
    (mem_outK.mp (hgenJ J hJ).2.2.2.2.1).2.1
  have hψinj : Set.InjOn ψ V := by
    intro J hJ J' hJ' hψψ
    by_contra hne
    obtain ⟨hcore, hp, hq, -, hψ, -, hval⟩ := hgenJ J hJ
    obtain ⟨hcore', -, -, -, -, -, hval'⟩ := hgenJ J' hJ'
    have hdot := F.dot_generic k₀ hcore hp (hq k₀) hψ hval hcore' hval'
    rw [hD.hcVV J hJ J' hJ' hne, ite_eq_left hψψ] at hdot
    exact mul_ne_zero (hγ0 J hJ) (hγ0 J' hJ') (by linarith)
  have hM0 : 0 < M := by omega
  have hss : s * s = 1 := sign_mul_self hs
  have hYs' : Ys = s • Y 0 := by
    rw [hsY, smul_smul, hss, one_smul]
  have hdYs : δ₀ * d i₀ + δ₁ * d i₁ - δ₂ * d i₂ - δ₃ * d i₃ = 0 := by
    have h1 : Ys ⬝ᵥ d = 0 := by
      rw [hYs', smul_dotProduct, hD.hYd 0 hM0, smul_zero]
    rw [dotProduct_comm, F.dot_Ys] at h1
    linarith
  have hdC : δ₀ * d i₀ - δ₁ * d i₁ + δ₂ * d i₂ - δ₃ * d i₃ + 2 * δ₄ * d i₄ = 0 := by
    have h1 := hD.hcd M M
    rw [dotProduct_comm, F.dot_C] at h1
    linarith
  have hdcore := F.dcore
  have hgdeg : ∀ J ∈ V, δ₀ * d i₀ - δ₁ * d i₁ + 2 * δ₄ * d i₄ + γ J * d (ψ J) = 0 := by
    intro J hJ
    obtain ⟨hcore, hp, hq, -, hψ, -, hval⟩ := hgenJ J hJ
    rw [← F.degree_generic k₀ hcore hp (hq k₀) hψ hval]
    exact hD.hcd _ _
  obtain ⟨J₀, hJ₀⟩ := hD.exists_mem_V
  have hgamma : ∀ J ∈ V, γ J = γ J₀ ∧ d (ψ J) = d (ψ J₀) := fun J hJ =>
    sign_pos_eq (hgenJ J hJ).2.2.2.1 (hgenJ J₀ hJ₀).2.2.2.1 (hd _) (hd _)
      (by linarith [hgdeg J hJ, hgdeg J₀ hJ₀])
  have hΔ0 : γ J₀ * d (ψ J₀) ≠ 0 := mul_ne_zero (hγ0 J₀ hJ₀) (hd _).ne'
  let col : Finset.Ico 1 M → Fin 2 → I → ℤ := fun k f =>
    if f = e k then c k.1 k.1 else c (k.1 + M) (k.1 + M)
  let sg : Finset.Ico 1 M → Fin 2 → ℤ := fun k f => if f = e k then σ k else σ' k
  have hcolpair : ∀ k f, PairAt (q k) (η k) (col k f) f (sg k f) := by
    intro k f
    by_cases hf : f = e k
    · simp only [col, sg, ite_eq_left hf]
      rw [hf]
      exact hpair k
    · simp only [col, sg, ite_eq_right hf]
      rw [eq_one_sub_of_ne hf]
      exact hpair' k
  have hcoloff : ∀ k f, OffPairs i₀ i₁ i₂ i₃ i₄ δ₀ δ₁ δ₂ δ₃ δ₄ p q k (col k f) 1 (ξ k) 0 := by
    intro k f
    by_cases hf : f = e k
    · simp only [col, ite_eq_left hf]
      exact hoff1 k
    · simp only [col, ite_eq_right hf]
      exact hoff1' k
  have hsg : ∀ k f, sg k f = 1 ∨ sg k f = -1 := by
    intro k f
    by_cases hf : f = e k
    · simp only [sg, ite_eq_left hf]
      exact hσ k
    · simp only [sg, ite_eq_right hf]
      exact hσ' k
  have hcold : ∀ k f, col k f ⬝ᵥ d = 0 := by
    intro k f
    by_cases hf : f = e k
    · simp only [col, ite_eq_left hf]
      exact hD.hcd _ _
    · simp only [col, ite_eq_right hf]
      exact hD.hcd _ _
  have hname := fun k f => F.pair_naming hd k f (hsg k f) (hcolpair k f)
    (by rw [← F.degree_diag (hcoloff k f) (hcolpair k f)]; exact hcold k f) hdYs hdC
  choose lP lQ hl hηP hηQ hdP hdQ hvP hvQ using hname
  let ξf : ℕ → I := fun h => if hh : h ∈ oddIdx m then p ⟨h, hh⟩ else i₀
  let Pf : ℕ → Fin 2 → I := fun r f =>
    if hr : r ∈ Finset.Ico 1 M then q ⟨r, hr⟩ (lP ⟨r, hr⟩ f) else i₀
  let Qf : ℕ → Fin 2 → I := fun r f =>
    if hr : r ∈ Finset.Ico 1 M then q ⟨r, hr⟩ (lQ ⟨r, hr⟩ f) else i₀
  have hξf : ∀ h (hh : h ∈ oddIdx m), ξf h = p ⟨h, hh⟩ := fun h hh => dite_eq_left hh
  have hPf : ∀ r (hr : r ∈ Finset.Ico 1 M) f, Pf r f = q ⟨r, hr⟩ (lP ⟨r, hr⟩ f) :=
    fun r hr f => dite_eq_left hr
  have hQf : ∀ r (hr : r ∈ Finset.Ico 1 M) f, Qf r f = q ⟨r, hr⟩ (lQ ⟨r, hr⟩ f) :=
    fun r hr f => dite_eq_left hr
  have hlP : ∀ k f, lP k f = pairA f ∨ lP k f = pairB f := fun k f => by
    rcases hl k f with ⟨h, -⟩ | ⟨h, -⟩
    · exact Or.inl h
    · exact Or.inr h
  have hlQ : ∀ k f, lQ k f = pairA f ∨ lQ k f = pairB f := fun k f => by
    rcases hl k f with ⟨-, h⟩ | ⟨-, h⟩
    · exact Or.inr h
    · exact Or.inl h
  have hlPQ : ∀ k f, lP k f ≠ lQ k f := fun k f => by
    rcases hl k f with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2]
    · exact pairA_ne_pairB f
    · exact (pairA_ne_pairB f).symm
  have hcover : ∀ k (l : Fin 4), ∃ f, l = lP k f ∨ l = lQ k f := by
    intro k l
    obtain ⟨f, hf⟩ := exists_pair l
    refine ⟨f, ?_⟩
    rcases hl k f with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hf with hf | hf <;> rw [hf]
    · exact Or.inl h1.symm
    · exact Or.inr h2.symm
    · exact Or.inr h2.symm
    · exact Or.inl h1.symm
  have hexh : ∀ i : I, i ∈ ({i₀, i₁, i₂, i₃, i₄} : Finset I) ∨ (∃ h, p h = i) ∨
      (∃ k l, q k l = i) ∨ ∃ J ∈ V, ψ J = i := by
    intro i
    by_contra hcon
    simp only [not_or, not_exists, not_and] at hcon
    obtain ⟨hic, hip, hiq, hiψ⟩ := hcon
    apply hD.hnv i 0 (hD.X_row_vanish G hic hip hiq)
    intro a b
    rw [ite_self]
    rcases orbit_reduction hD.hm c hD.hcsymm V hD.hVrep a b with ⟨rfl, rfl⟩ |
      ⟨ρ, hρ, hab, -⟩ | ⟨J, hJ, hab, -⟩
    · rw [hD.hc00]
      rfl
    · rw [hab]
      by_cases hρM : ρ = M
      · rw [hρM]
        exact (F.frame_vanish hic hip hiq).2.2
      · obtain ⟨r, hr, hρr | hρr⟩ := diag_index hD.hm hρ hρM
        · rw [hρr, (hoff1 ⟨r, hr⟩).2.2.1 i (mem_outK.mpr ⟨hic, hip, hiq ⟨r, hr⟩⟩), ite_self]
        · rw [hρr, (hoff1' ⟨r, hr⟩).2.2.1 i (mem_outK.mpr ⟨hic, hip, hiq ⟨r, hr⟩⟩), ite_self]
    · rw [hab, (hgenJ J hJ).2.2.2.2.2.2 i (mem_outK.mpr ⟨hic, hip, hiq k₀⟩),
        ite_eq_right (fun h => hiψ J hJ h.symm)]
  refine ⟨δ₀, δ₁, δ₂, δ₃, δ₄, α, s, γ J₀, i₀, i₁, i₂, i₃, i₄, ξf, Pf, Qf, ψ, D, d (ψ J₀),
    ?_⟩
  intro Acol Kc core evenFam
  have hPmem : ∀ r (hr : r ∈ Finset.Ico 1 M) f, Pf r f ∈ evenFam := fun r hr f =>
    Finset.mem_union_left _ (Finset.mem_image.mpr ⟨(r, f), Finset.mem_product.mpr
      ⟨hr, Finset.mem_univ _⟩, rfl⟩)
  have hQmem : ∀ r (hr : r ∈ Finset.Ico 1 M) f, Qf r f ∈ evenFam := fun r hr f =>
    Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(r, f), Finset.mem_product.mpr
      ⟨hr, Finset.mem_univ _⟩, rfl⟩)
  have hevenFam : ∀ i ∈ evenFam, ∃ k l, q k l = i := by
    intro i hi
    rcases Finset.mem_union.mp hi with hi | hi <;>
      obtain ⟨⟨r, f⟩, hrf, rfl⟩ := Finset.mem_image.mp hi <;>
      have hr := (Finset.mem_product.mp hrf).1
    · exact ⟨⟨r, hr⟩, lP ⟨r, hr⟩ f, (hPf r hr f).symm⟩
    · exact ⟨⟨r, hr⟩, lQ ⟨r, hr⟩ f, (hQf r hr f).symm⟩
  have hξimage : ∀ i ∈ (oddIdx m).image ξf, ∃ h, p h = i := by
    intro i hi
    obtain ⟨h, hh, rfl⟩ := Finset.mem_image.mp hi
    exact ⟨⟨h, hh⟩, (hξf h hh).symm⟩
  have injξ : Set.InjOn ξf (oddIdx m) := by
    intro h hh h' hh' heq
    rw [hξf h hh, hξf h' hh'] at heq
    exact congrArg Subtype.val (F.p_inj heq)
  have injPQ : ∀ r ∈ Finset.Ico 1 M, ∀ r' ∈ Finset.Ico 1 M, ∀ e e' : Fin 2,
      (Pf r e = Pf r' e' → r = r' ∧ e = e') ∧ (Qf r e = Qf r' e' → r = r' ∧ e = e') ∧
        Pf r e ≠ Qf r' e' := by
    intro r hr r' hr' f f'
    simp only [hPf r hr, hPf r' hr', hQf r hr, hQf r' hr']
    refine ⟨fun heq => ?_, fun heq => ?_, fun heq => ?_⟩
    · obtain ⟨hk, hll⟩ := F.q_inj heq
      have hrr : r = r' := congrArg Subtype.val hk
      subst hrr
      refine ⟨rfl, pair_unique (hlP ⟨r, hr⟩ f) ?_⟩
      rw [hll]
      exact hlP ⟨r, hr'⟩ f'
    · obtain ⟨hk, hll⟩ := F.q_inj heq
      have hrr : r = r' := congrArg Subtype.val hk
      subst hrr
      refine ⟨rfl, pair_unique (hlQ ⟨r, hr⟩ f) ?_⟩
      rw [hll]
      exact hlQ ⟨r, hr'⟩ f'
    · obtain ⟨hk, hll⟩ := F.q_inj heq
      have hrr : r = r' := congrArg Subtype.val hk
      subst hrr
      have hff : f = f' := pair_unique (hlP ⟨r, hr⟩ f) (by rw [hll]; exact hlQ ⟨r, hr'⟩ f')
      subst hff
      exact hlPQ ⟨r, hr⟩ f hll
  have ξcore : ∀ h ∈ oddIdx m, ξf h ∉ core := by
    intro h hh
    rw [hξf h hh]
    exact F.p_notMem_core _
  have PQcore : ∀ r ∈ Finset.Ico 1 M, ∀ f, Pf r f ∉ core ∧ Qf r f ∉ core ∧
      Pf r f ∉ (oddIdx m).image ξf ∧ Qf r f ∉ (oddIdx m).image ξf := by
    intro r hr f
    rw [hPf r hr, hQf r hr]
    refine ⟨F.q_notMem_core _ _, F.q_notMem_core _ _, fun hmem => ?_, fun hmem => ?_⟩
    · obtain ⟨h, hh⟩ := hξimage _ hmem
      exact F.q_ne_p _ _ h hh.symm
    · obtain ⟨h, hh⟩ := hξimage _ hmem
      exact F.q_ne_p _ _ h hh.symm
  have ψfam : ∀ J ∈ V, ψ J ∉ core ∧ ψ J ∉ (oddIdx m).image ξf ∧ ψ J ∉ evenFam := by
    intro J hJ
    refine ⟨hψc J hJ, fun hmem => ?_, fun hmem => ?_⟩
    · obtain ⟨h, hh⟩ := hξimage _ hmem
      exact hψp J hJ h hh
    · obtain ⟨k, l, hkl⟩ := hevenFam _ hmem
      exact hψq J hJ k l hkl
  have exh : Finset.univ = core ∪ (oddIdx m).image ξf ∪ evenFam ∪ V.image ψ := by
    ext i
    simp only [Finset.mem_univ, true_iff]
    rcases hexh i with hi | ⟨h, rfl⟩ | ⟨k, l, rfl⟩ | ⟨J, hJ, rfl⟩
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ hi))
    · refine Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ ?_))
      exact Finset.mem_image.mpr ⟨h.1, h.2, hξf h.1 h.2⟩
    · refine Finset.mem_union_left _ (Finset.mem_union_right _ ?_)
      obtain ⟨f, hf | hf⟩ := hcover k l
      · have h := hPmem k.1 k.2 f
        rwa [hPf k.1 k.2 f, ← hf] at h
      · have h := hQmem k.1 k.2 f
        rwa [hQf k.1 k.2 f, ← hf] at h
    · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨J, hJ, rfl⟩)
  have card : Fintype.card I = (m ^ 2 + 12 * m + 8) / 6 := by
    rw [← Finset.card_univ, exh]
    have d1 : Disjoint (core ∪ (oddIdx m).image ξf ∪ evenFam) (V.image ψ) := by
      rw [Finset.disjoint_right]
      intro i hi
      obtain ⟨J, hJ, rfl⟩ := Finset.mem_image.mp hi
      obtain ⟨h1, h2, h3⟩ := ψfam J hJ
      simp only [Finset.mem_union, not_or]
      exact ⟨⟨h1, h2⟩, h3⟩
    have d2 : Disjoint (core ∪ (oddIdx m).image ξf) evenFam := by
      rw [Finset.disjoint_right]
      intro i hi
      simp only [Finset.mem_union, not_or]
      rcases Finset.mem_union.mp hi with hi | hi <;>
        obtain ⟨⟨r, f⟩, hrf, rfl⟩ := Finset.mem_image.mp hi <;>
        have hr := (Finset.mem_product.mp hrf).1
      · exact ⟨(PQcore r hr f).1, (PQcore r hr f).2.2.1⟩
      · exact ⟨(PQcore r hr f).2.1, (PQcore r hr f).2.2.2⟩
    have d3 : Disjoint core ((oddIdx m).image ξf) := by
      rw [Finset.disjoint_right]
      intro i hi
      obtain ⟨h, hh, rfl⟩ := Finset.mem_image.mp hi
      exact ξcore h hh
    have d4 : Disjoint
        (((Finset.Ico 1 M) ×ˢ (Finset.univ : Finset (Fin 2))).image (fun x => Pf x.1 x.2))
        (((Finset.Ico 1 M) ×ˢ (Finset.univ : Finset (Fin 2))).image (fun x => Qf x.1 x.2)) := by
      rw [Finset.disjoint_left]
      intro i hi hi'
      obtain ⟨⟨r, f⟩, hrf, rfl⟩ := Finset.mem_image.mp hi
      obtain ⟨⟨r', f'⟩, hrf', he⟩ := Finset.mem_image.mp hi'
      exact (injPQ r (Finset.mem_product.mp hrf).1 r' (Finset.mem_product.mp hrf').1 f
        f').2.2 he.symm
    rw [Finset.card_union_of_disjoint d1, Finset.card_union_of_disjoint d2,
      Finset.card_union_of_disjoint d3, Finset.card_union_of_disjoint d4]
    have c0 : core.card = 5 := by
      show ({i₀, i₁, i₂, i₃, i₄} : Finset I).card = 5
      rw [Finset.card_insert_of_notMem (by simp [h01, h02, h03, h04]),
        Finset.card_insert_of_notMem (by simp [h12, h13, h14]),
        Finset.card_insert_of_notMem (by simp [h23, h24]), Finset.card_pair h34]
    have c1 : ((oddIdx m).image ξf).card = M := by
      rw [Finset.card_image_of_injOn injξ, hD.card_oddIdx]
    have cP : (((Finset.Ico 1 M) ×ˢ (Finset.univ : Finset (Fin 2))).image
        (fun x => Pf x.1 x.2)).card = (M - 1) * 2 := by
      rw [Finset.card_image_of_injOn, Finset.card_product, Nat.card_Ico, Finset.card_univ,
        Fintype.card_fin]
      intro x hx x' hx' he
      have hx1 := (Finset.mem_product.mp (Finset.mem_coe.mp hx)).1
      have hx1' := (Finset.mem_product.mp (Finset.mem_coe.mp hx')).1
      obtain ⟨h1, h2⟩ := (injPQ x.1 hx1 x'.1 hx1' x.2 x'.2).1 he
      exact Prod.ext h1 h2
    have cQ : (((Finset.Ico 1 M) ×ˢ (Finset.univ : Finset (Fin 2))).image
        (fun x => Qf x.1 x.2)).card = (M - 1) * 2 := by
      rw [Finset.card_image_of_injOn, Finset.card_product, Nat.card_Ico, Finset.card_univ,
        Fintype.card_fin]
      intro x hx x' hx' he
      have hx1 := (Finset.mem_product.mp (Finset.mem_coe.mp hx)).1
      have hx1' := (Finset.mem_product.mp (Finset.mem_coe.mp hx')).1
      obtain ⟨h1, h2⟩ := (injPQ x.1 hx1 x'.1 hx1' x.2 x'.2).2.1 he
      exact Prod.ext h1 h2
    have cV : (V.image ψ).card = (m - 1) * (m - 2) / 6 := by
      rw [Finset.card_image_of_injOn hψinj]
      obtain ⟨n, -, rfl⟩ := hD.pow
      exact card_reps V hD.hV6 hD.hVrep
    rw [c0, c1, cP, cQ, cV]
    obtain ⟨n, hn, hmn⟩ := hD.pow
    have hce := count_eq (n := n) (by omega)
    rw [← hmn] at hce
    rw [← hce]
    have hMm : m / 2 = M := by omega
    rw [hMm]
    generalize (m - 1) * (m - 2) / 6 = t
    omega
  refine ⟨?signs, F.core_inj, injξ, injPQ, hψinj, ξcore, PQcore, ψfam, exh, card,
    ?formX, ?formY0, ?formC, ?formE, ?formYr, ?formDiag, ?formGen, F.Dpos, hd _, ?degξ, ?degPQ,
    ?degψ, by linarith, by linarith, by linarith, by linarith, ?gen, ?ne⟩
  case signs =>
    intro t ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact F.sδ₀
    · exact F.sδ₁
    · exact F.sδ₂
    · exact F.sδ₃
    · exact F.sδ₄
    · exact F.sα
    · exact hs
    · exact (hgenJ J₀ hJ₀).2.2.2.1
  case formX =>
    intro h hh
    rw [hξf h hh]
    exact F.formA ⟨h, hh⟩
  case formY0 =>
    rw [hsY, F.formYs]
  case formC =>
    rw [show c (M : ZMod m) (M : ZMod m) = _ from F.formC]
    simp only [Kc]
    abel
  case formE =>
    intro r hr
    have h := F.E_explicit ⟨r, hr⟩ (hl ⟨r, hr⟩) (hηP ⟨r, hr⟩) (hηQ ⟨r, hr⟩)
    simp only at h
    rw [h, hPf r hr, hPf r hr, hQf r hr, hQf r hr]
  case formYr =>
    intro r hr
    have h := F.Y_explicit ⟨r, hr⟩ (hl ⟨r, hr⟩) (hηP ⟨r, hr⟩) (hηQ ⟨r, hr⟩)
    simp only at h
    rw [h, hPf r hr, hPf r hr, hQf r hr, hQf r hr]
  case formDiag =>
    intro r hr
    set k : Finset.Ico 1 M := ⟨r, hr⟩ with hkdef
    refine ⟨e k, ?_, ?_⟩
    · have h := F.diag_explicit (hcoloff k (e k)) (hcolpair k (e k)) (hl k (e k))
        (hvP k (e k)) (hvQ k (e k))
      simp only [col, ite_eq_left rfl] at h
      rw [hPf r hr, hQf r hr]
      exact h
    · have h := F.diag_explicit (hcoloff k (1 - e k)) (hcolpair k (1 - e k)) (hl k (1 - e k))
        (hvP k (1 - e k)) (hvQ k (1 - e k))
      simp only [col, ite_eq_right (one_sub_ne (e k))] at h
      rw [hPf r hr, hQf r hr]
      exact h
  case formGen =>
    intro J hJ
    obtain ⟨hcore, hp, hq, -, hψ, -, hval⟩ := hgenJ J hJ
    rw [F.generic_explicit hcore hp (hq k₀) hψ hval, (hgamma J hJ).1]
  case degξ =>
    intro h hh
    rw [hξf h hh]
    exact F.dp _
  case degPQ =>
    intro r hr f
    rw [hPf r hr, hQf r hr]
    exact ⟨hdP _ f, hdQ _ f⟩
  case degψ =>
    intro J hJ
    exact (hgamma J hJ).2
  case gen =>
    linarith [hgdeg J₀ hJ₀]
  case ne =>
    intro h
    apply hΔ0
    linarith [hgdeg J₀ hJ₀]

theorem complete (hD : ColumnData m M d X Y c V) : CompleteSupport m M d X Y c V := by
  obtain ⟨i₀, i₁, i₂, i₃, i₄, p, q, δ₀, δ₁, δ₂, δ₃, δ₄, α, η, D, F⟩ := hD.exists_frame
  have G : FlatFrame m M d X Y c (Y 0) i₀ i₁ i₂ i₃ i₄ p q δ₀ δ₁ δ₂ δ₃ δ₄ α η D :=
    ⟨F, Or.inl rfl⟩
  have hM2 := hD.two_le_M
  have hk₀ : 1 ∈ Finset.Ico 1 M := Finset.mem_Ico.mpr ⟨le_rfl, by omega⟩
  obtain ⟨a, e, σ, σ', ξ, x, -, -, hx, hoff, -, -, -⟩ := hD.diag_data G ⟨1, hk₀⟩
  have hall : ∀ k : Finset.Ico 1 M, CoreAt i₀ i₁ i₂ i₃ i₄ δ₀ δ₁ δ₂ δ₃ δ₄ a (c k.1 k.1) := by
    intro k
    obtain ⟨a', e', τ, τ', ξ', x', -, -, hx', hoff', -, -, -⟩ := hD.diag_data G k
    rw [(hD.case_uniform G hx hx' hoff hoff').1]
    exact hoff'.1
  rcases (show a = 0 ∨ a = 1 ∨ a = 2 by fin_cases a <;> simp) with rfl | rfl | rfl
  · exact absurd (hD.not_caseA G ⟨1, hk₀⟩ (hall _)) id
  · exact hD.complete_of_B1 G (s := 1) (Or.inl rfl) (by rw [one_smul]) hall
  · exact hD.complete_of_B1 G.swap (s := -1) (Or.inr rfl) (by rw [neg_smul, one_smul, neg_neg])
      fun k => (hall k).swap

end ColumnData

end CFSG.Wreathed.FlatComplete
