module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I107Of
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Basic

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open scoped commutatorElement

theorem pRank_le_of_card_le {G : Type} [Group G] [Finite G] {p : ℕ} (hp : 2 ≤ p) {H : Subgroup G} {r : ℕ}
    (h : ∀ E : Subgroup G, E ≤ H → IsElemAbelian p E → Nat.card E ≤ p ^ r) :
    CFSG.Open.pRank p H ≤ r := by
  unfold CFSG.Open.pRank
  apply csSup_le'
  intro k hk
  obtain ⟨E, hEH, hE, hk⟩ := hk
  have hle : p ^ k ≤ p ^ r := hk ▸ h E hEH hE
  exact (Nat.pow_le_pow_iff_right (by omega : 1 < p)).1 hle

theorem isElemAbelian_map_of_injective {G H : Type} [Group G] [Group H] (f : G →* H)
    (hf : Function.Injective f) {p : ℕ} {E : Subgroup G} (hE : IsElemAbelian p E) :
    IsElemAbelian p (E.map f) := by
  refine ⟨⟨⟨fun x y => ?_⟩⟩, ?_⟩
  · obtain ⟨a, ha, ha'⟩ := Subgroup.mem_map.1 x.2
    obtain ⟨b, hb, hb'⟩ := Subgroup.mem_map.1 y.2
    apply Subtype.ext
    show (x : H) * (y : H) = (y : H) * (x : H)
    have hc : a * b = b * a := congrArg Subtype.val (hE.1.is_comm.comm (⟨a, ha⟩ : E) ⟨b, hb⟩)
    rw [← ha', ← hb', ← map_mul, ← map_mul, hc]
  · intro x hx
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.1 hx
    rw [← map_pow, hE.2 a ha, map_one]

theorem rk2IsLabel_rawDatum {S : Type} [Group S] {lab : GLALabel} (h : Rk2IsLabel S lab) :
    GLARawDatum lab (fun R _ _ _ => IsSimpleGroup R ∧ (∃ a b : R, a * b ≠ b * a) ∧
      Nonempty (S ⧸ Subgroup.center S ≃* R)) := by
  obtain ⟨-, lab0, -, hraw⟩ := h
  obtain ⟨R, _, I, F, hQ⟩ := rk2_rawDatum_exists hraw
  have hl : lab0 = lab := hQ.2.2.choose_spec
  subst hl
  refine rk2_rawDatum_mono ?_ hraw
  rintro R' _ I' F' ⟨hs, hna, θ, -⟩
  exact ⟨hs, hna, ⟨θ⟩⟩

theorem center_eq_bot_of_quotient_nonab {S R : Type} [Group S] [Group R] [IsSimpleGroup S]
    (θ : S ⧸ Subgroup.center S ≃* R) (hna : ∃ a b : R, a * b ≠ b * a) :
    Subgroup.center S = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center S) with h | h
  · exact h
  · exfalso
    have hcomm : ∀ x y : S ⧸ Subgroup.center S, x * y = y * x := by
      intro x y
      obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
      obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      apply QuotientGroup.eq.2
      rw [h]
      exact Subgroup.mem_top _
    obtain ⟨a, b, hab⟩ := hna
    apply hab
    obtain ⟨x, rfl⟩ := θ.surjective a
    obtain ⟨y, rfl⟩ := θ.surjective b
    rw [← map_mul, ← map_mul, hcomm x y]

@[expose] def outBonus107 (lab : GLALabel) (p : ℕ) : ℕ :=
  (if p ∣ lab.n then 1 else 0) + (if p = 3 ∧ ((lab.tag = .D ∧ lab.rank = 4) ∨ lab.tag = .triD4) then 1 else 0)

theorem upA107_eq (lab : GLALabel) (p : ℕ) :
    upA107 lab p = rk2Mult lab (rk2Ord p lab.n) + outBonus107 lab p := by
  simp only [upA107, outBonus107, Nat.add_assoc]

@[expose] def OutRank107 : Prop :=
  ∀ (lab : GLALabel), GLAInLambda2 lab → ∀ p : ℕ, p.Prime → p ≠ 2 →
    Rk2LabelAll lab fun R [Group R] I _ => IsSimpleGroup R → (∃ a b : R, a * b ≠ b * a) →
      ∀ E : Subgroup (MulAut R), IsElemAbelian p E →
        Nat.card E ≤
          Nat.card ↥(E ⊓ Subgroup.closure (I ∪ Set.range (MulAut.conj : R →* MulAut R))) * p ^ outBonus107 lab p

theorem i107AutAt_of_rk2 (hInn : Rk2InnRank) (hOut : OutRank107) : I107AutAt := by
  intro S _ _ lab p hS hrk hlab hp hp2
  have hraw := rk2IsLabel_rawDatum hrk
  have h1 := hInn lab hlab trivial p hp hp2 _ hraw
  have h2 := hOut lab hlab p hp hp2 _ h1
  obtain ⟨R, instR, I, F, hQ⟩ := rk2_rawDatum_exists h2
  obtain ⟨⟨⟨hsR, hnaR, ⟨θ⟩⟩, hPinn⟩, hPout⟩ := hQ
  have hZ : Subgroup.center S = ⊥ := center_eq_bot_of_quotient_nonab θ hnaR
  let e₀ : S ⧸ Subgroup.center S ≃* S :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  let e : S ≃* R := e₀.symm.trans θ
  refine pRank_le_of_card_le hp.two_le ?_
  intro E _ hE
  let φ : MulAut S ≃* MulAut R := MulAut.congr e
  let E' : Subgroup (MulAut R) := E.map φ.toMonoidHom
  have hE' : IsElemAbelian p E' := isElemAbelian_map_of_injective φ.toMonoidHom φ.injective hE
  have hcard : Nat.card E' = Nat.card E := Subgroup.card_map_of_injective φ.injective
  have hO := hPout hsR hnaR E' hE'
  have hI := hPinn hsR (E' ⊓ Subgroup.closure (I ∪ Set.range (MulAut.conj : R →* MulAut R))) inf_le_right
    (isElemAbelian_mono hE' inf_le_left)
  rw [hcard] at hO
  rw [upA107_eq]
  calc Nat.card E ≤ Nat.card ↥(E' ⊓ Subgroup.closure (I ∪ Set.range (MulAut.conj : R →* MulAut R))) *
        p ^ outBonus107 lab p := hO
    _ ≤ p ^ rk2Mult lab (rk2Ord p lab.n) * p ^ outBonus107 lab p := Nat.mul_le_mul_right _ hI
    _ = p ^ (rk2Mult lab (rk2Ord p lab.n) + outBonus107 lab p) := (pow_add _ _ _).symm

theorem i107AutAt_holds (hInn : Rk2InnRank) (hOut : OutRank107) : I107AutAt :=
  i107AutAt_of_rk2 hInn hOut

end CFSG.LocalAnalysis.GLTheoremA

end
