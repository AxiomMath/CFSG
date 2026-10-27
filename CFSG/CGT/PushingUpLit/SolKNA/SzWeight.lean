module

public import CFSG.CGT.PushingUpLit.SolKNA.SzNatural
public import CFSG.CGT.PushingUpLit.SolKNA.SzRepAux
public import CFSG.CGT.PushingUpLit.SolKNA.SzSimple

public section

namespace CFSG.CGT.PushingUpLit.SolKNA

open CFSG.Open CFSG.RankThree.GF2n.SzExplicit Matrix

theorem weight_induction (h : SzFpfSimpleNatural) {a : ℕ} (ha : 1 ≤ a) :
    ∀ (n : ℕ) (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
      (ρ : Representation (ZMod 2) ↥(Sz a) V), Nat.card V ≤ n →
      (∃ g : ↥(Sz a), orderOf g = 5 ∧ ∀ v, ρ g v = v → v = 0) →
      ∀ c : F a → F a → V, (∀ b b' b'', c (b + b') b'' = c b b'' + c b' b'') →
        (∀ b b' b'', c b (b' + b'') = c b b' + c b b'') → (∀ b, c b b = 0) →
        (∀ α β b b', ρ (rootSz a α β) (c b b') = c b b') →
        (∀ (x : (F a)ˣ) b b', ρ (torusSz a x) (c b b') =
          c ((x : F a) ^ (1 + 2 ^ (a + 1)) * b) ((x : F a) ^ (1 + 2 ^ (a + 1)) * b')) →
        ∀ b b', c b b' = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro V _ _ _ ρ hn hfpf c h₁ h₂ halt hS hT
    by_cases hsub : Subsingleton V
    · intro b b'
      exact Subsingleton.elim _ _
    have hnt : Nontrivial V := not_subsingleton_iff_nontrivial.mp hsub
    obtain ⟨W, hWinv, hWtop, hWmax⟩ := exists_maximal_invariant ρ
    obtain ⟨g, hgord, hgfpf⟩ := hfpf
    have hg5 : g ^ 5 = 1 := by rw [← hgord]; exact pow_orderOf_eq_one g
    let ρQ := ρ.quotient W (fun k w hw => hWinv k w hw)
    have hqa : ∀ (k : ↥(Sz a)) (x : V), ρQ k (W.mkQ x) = W.mkQ (ρ k x) := fun k x => by
      simp [ρQ]
    have hfpfQ : ∀ v, ρQ g v = v → v = 0 := fpf_quotient ρ W hWinv hg5 hgfpf
    have hirr := quotient_irreducible ρ W hWinv hWmax
    have hntQ : Nontrivial (V ⧸ W) := Submodule.Quotient.nontrivial_iff.mpr hWtop
    have hfinQ : Finite (V ⧸ W) := Finite.of_surjective W.mkQ (Submodule.mkQ_surjective W)
    obtain ⟨θ, hθb, hθ⟩ := h a ha (V ⧸ W) ρQ ⟨g, hgord, hfpfQ⟩ hntQ hirr
    have hc0 : ∀ b b', W.mkQ (c b b') = 0 :=
      natural_case ha ρQ θ hθb hθ (fun b b' => W.mkQ (c b b'))
        (fun b b' b'' => by rw [h₁, map_add]) (fun b b' b'' => by rw [h₂, map_add])
        (fun b => by rw [halt, map_zero])
        (fun α β b b' => by rw [hqa, hS]) (fun x b b' => by rw [hqa, hT])
    have hcW : ∀ b b', c b b' ∈ W := fun b b' => (Submodule.Quotient.mk_eq_zero W).mp (hc0 b b')
    obtain ⟨x, hx⟩ : ∃ x : V, x ∉ W := by
      by_contra hcon
      exact hWtop (eq_top_iff.mpr fun y _ => by_contra fun hy => hcon ⟨y, hy⟩)
    have hlt : Nat.card W < Nat.card V := Finite.card_subtype_lt (p := (· ∈ W)) hx
    have hz := ih (Nat.card W) (lt_of_lt_of_le hlt hn) W (restrictRep ρ W hWinv) le_rfl
      ⟨g, hgord, fpf_restrict ρ W hWinv hgfpf⟩ (fun b b' => ⟨c b b', hcW b b'⟩)
      (fun b b' b'' => Subtype.ext (h₁ b b' b'')) (fun b b' b'' => Subtype.ext (h₂ b b' b''))
      (fun b => Subtype.ext (halt b)) (fun α β b b' => Subtype.ext (hS α β b b'))
      (fun x b b' => Subtype.ext (hT x b b'))
    intro b b'
    exact congrArg Subtype.val (hz b b')

theorem szCommutatorWeight_of_simple (h : SzFpfSimpleNatural) : SzCommutatorWeight := by
  intro a ha g₀ V _ _ _ ρ hfpf c h₁ h₂ halt hS hT
  let ρ' : Representation (ZMod 2) ↥(Sz a) V := ρ.comp (MulAut.conj g₀).toMonoidHom
  have hfpf' : ∃ g : ↥(Sz a), orderOf g = 5 ∧ ∀ v, ρ' g v = v → v = 0 := by
    obtain ⟨g, hg5, hg⟩ := hfpf
    refine ⟨g₀⁻¹ * g * g₀, ?_, fun v hv => hg v ?_⟩
    · rw [← hg5]
      have := orderOf_injective (MulAut.conj g₀⁻¹).toMonoidHom (MulAut.conj g₀⁻¹).injective g
      simpa [MulAut.conj_apply] using this
    · simpa [ρ', MulAut.conj_apply, mul_assoc] using hv
  exact weight_induction h ha _ V ρ' le_rfl hfpf' c h₁ h₂ halt
    (fun α β b b' => by simpa [ρ', MulAut.conj_apply] using hS α β b b')
    (fun x b b' => by simpa [ρ', MulAut.conj_apply] using hT x b b')

end CFSG.CGT.PushingUpLit.SolKNA
