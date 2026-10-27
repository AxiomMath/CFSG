module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesRankPDimCore
public import CFSG.LocalAnalysis.SectionRank.Ccomm.ElementaryAut

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.RankP

open Subgroup Module

theorem central_commutator_pow {P : Type*} [Group P] {a b c : P} (hc : ∀ g : P, c * g = g * c)
    (hrel : c * (b * a) = a * b) (n : ℕ) : c ^ n * (b ^ n * a) = a * b ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hcb : ∀ m : ℕ, b ^ m * c = c * b ^ m := fun m => (hc (b ^ m)).symm
    symm
    calc a * b ^ (n + 1) = a * b ^ n * b := by rw [pow_succ, ← mul_assoc]
      _ = (c ^ n * (b ^ n * a)) * b := by rw [ih]
      _ = c ^ n * (b ^ n * (a * b)) := by simp only [mul_assoc]
      _ = c ^ n * (b ^ n * (c * (b * a))) := by rw [hrel]
      _ = c ^ n * (c * (b ^ n * (b * a))) := by
          rw [← mul_assoc (b ^ n) c, hcb n, mul_assoc c]
      _ = c ^ (n + 1) * (b ^ (n + 1) * a) := by simp only [pow_succ, mul_assoc]

theorem exists_central_commutator {p : ℕ} [Fact p.Prime] {P : Type*} [Group P] [Finite P]
    (hP : IsPGroup p P) (hnc : ¬ ∀ a b : P, a * b = b * a) :
    ∃ a b c : P, c * (b * a) = a * b ∧ (∀ g : P, c * g = g * c) ∧ c ^ p = 1 ∧ c ≠ 1 := by
  have hZtop : center P ≠ ⊤ := fun h => hnc fun a b => by
    have : a ∈ center P := h ▸ mem_top a
    exact (mem_center_iff.mp this b).symm
  haveI : Nontrivial (P ⧸ center P) := by
    rw [QuotientGroup.nontrivial_iff]
    exact hZtop
  have hPq : IsPGroup p (P ⧸ center P) := hP.to_quotient _
  haveI := hPq.center_nontrivial
  obtain ⟨⟨ā, hā⟩, hne⟩ := exists_ne (1 : center (P ⧸ center P))
  have hā1 : ā ≠ 1 := fun h => hne (Subtype.ext h)
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective ā
  have hcomm : ∀ g : P, a * g * a⁻¹ * g⁻¹ ∈ center P := by
    intro g
    rw [← QuotientGroup.eq_one_iff]
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    have := mem_center_iff.mp hā (g : P ⧸ center P)
    rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul]
    exact this.symm
  have hanot : a ∉ center P := fun h => hā1 ((QuotientGroup.eq_one_iff a).mpr h)
  obtain ⟨b, hb⟩ : ∃ b : P, b * a ≠ a * b := by
    by_contra h
    push Not at h
    exact hanot (mem_center_iff.mpr h)
  set c₀ : P := a * b * a⁻¹ * b⁻¹ with hc₀
  have hc₀Z : c₀ ∈ center P := hcomm b
  have hc₀c : ∀ g : P, c₀ * g = g * c₀ := fun g => (mem_center_iff.mp hc₀Z g).symm
  have hc₀1 : c₀ ≠ 1 := by
    intro h
    apply hb
    have : a * b * a⁻¹ * b⁻¹ = 1 := h
    rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at this
    exact this.symm
  have hrel₀ : c₀ * (b * a) = a * b := by rw [hc₀]; group
  obtain ⟨m, hm⟩ := (IsPGroup.iff_orderOf.mp hP) c₀
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hc₀1 (orderOf_eq_one_iff.mp (by simpa using hm))
  have hdvd : p ^ (m - 1) ∣ orderOf c₀ := by
    rw [hm]
    exact pow_dvd_pow p (Nat.sub_le m 1)
  have hord : orderOf (c₀ ^ p ^ (m - 1)) = p := by
    rw [orderOf_pow_of_dvd (pow_ne_zero _ (Fact.out : p.Prime).ne_zero) hdvd, hm]
    rw [Nat.pow_div (Nat.sub_le m 1) (Fact.out : p.Prime).pos]
    have : m - (m - 1) = 1 := by omega
    rw [this, pow_one]
  refine ⟨a, b ^ p ^ (m - 1), c₀ ^ p ^ (m - 1), ?_, fun g => ?_, ?_, ?_⟩
  · exact central_commutator_pow hc₀c hrel₀ _
  · exact (Commute.pow_left (show Commute c₀ g from hc₀c g) _).eq
  · have := pow_orderOf_eq_one (c₀ ^ p ^ (m - 1))
    rwa [hord] at this
  · intro h
    rw [h, orderOf_one] at hord
    exact (Fact.out : p.Prime).one_lt.ne hord

theorem finrank_ge_of_faithful_nonabelian {f p : ℕ} [Fact f.Prime] [Fact p.Prime] (hfp : f ≠ p)
    {V : Type*} [AddCommGroup V] [Module (ZMod f) V] [Module.Finite (ZMod f) V]
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup p P) (ρ : P →* Module.End (ZMod f) V)
    (hρ : ∀ g : P, ρ g = 1 → g = 1) (hnc : ¬ ∀ a b : P, a * b = b * a) :
    p ≤ finrank (ZMod f) V := by
  classical
  obtain ⟨a, b, c, hrel, hcc, hcp, hc1⟩ := exists_central_commutator hP hnc
  have hp : (p : ZMod f) ≠ 0 := by
    intro h
    rw [ZMod.natCast_eq_zero_iff] at h
    exact hfp ((Nat.prime_dvd_prime_iff_eq (Fact.out) (Fact.out)).mp h)
  have hρc : ∃ v : V, ρ c v ≠ v := by
    by_contra h
    push Not at h
    exact hc1 (hρ c (LinearMap.ext fun v => by simpa using h v))
  haveI : Finite V := Module.finite_of_finite (ZMod f)
  let S : Set (Submodule (ZMod f) V) :=
    {W | (∀ g : P, ∀ v ∈ W, ρ g v ∈ W) ∧ ∃ v ∈ W, ρ c v ≠ v}
  obtain ⟨v₀, hv₀⟩ := hρc
  have hSne : S.Nonempty := ⟨⊤, fun g v _ => Submodule.mem_top, v₀, Submodule.mem_top, hv₀⟩
  obtain ⟨W, ⟨hWinv, hWc⟩, hWmin⟩ :=
    (wellFounded_lt (α := Submodule (ZMod f) V)).has_min S hSne
  let ρU : P →* Module.End (ZMod f) W :=
    { toFun := fun g => (ρ g).restrict (fun v hv => hWinv g v hv)
      map_one' := by
        ext w
        simp
      map_mul' := fun g h => by
        ext w
        simp }
  have hρU : ∀ g (w : W), ((ρU g w : W) : V) = ρ g (w : V) := fun g w => rfl
  have hminU : ∀ W' : Submodule (ZMod f) W, (∀ g : P, ∀ u ∈ W', ρU g u ∈ W') →
      (∃ u ∈ W', ρU c u ≠ u) → W' = ⊤ := by
    intro W' hinv ⟨u, huW', hu⟩
    have hmem : W'.map W.subtype ∈ S := by
      refine ⟨?_, ?_⟩
      · rintro g _ ⟨u, hu, rfl⟩
        exact ⟨ρU g u, hinv g u hu, rfl⟩
      · refine ⟨(u : V), ⟨u, huW', rfl⟩, fun h => hu (Subtype.ext ?_)⟩
        rw [hρU]
        exact h
    have hle : W'.map W.subtype ≤ W := Submodule.map_subtype_le W W'
    have heq : W'.map W.subtype = W := by
      by_contra hne
      exact hWmin _ hmem (lt_of_le_of_ne hle hne)
    apply Submodule.map_injective_of_injective W.injective_subtype
    rw [heq, Submodule.map_subtype_top]
  have hWc' : ∃ u : W, ρU c u ≠ u := by
    obtain ⟨v, hvW, hv⟩ := hWc
    exact ⟨⟨v, hvW⟩, fun h => hv (congrArg Subtype.val h)⟩
  have hρUcc : ∀ g : P, c * g = g * c := hcc
  have key := finrank_ge_of_minimal (k := ZMod f) hp ρU hcc hrel hcp hminU hWc'
  exact key.trans (Submodule.finrank_le W)

theorem card_ge_of_faithful_nonabelian {f p : ℕ} (hf : f.Prime) (hp : p.Prime) (hfp : f ≠ p)
    {W : Type*} [Group W] [Finite W] (hcomm : ∀ a b : W, a * b = b * a)
    (hpow : ∀ a : W, a ^ f = 1) {P : Type*} [Group P] [Finite P] (hP : IsPGroup p P)
    (ρ : P →* MulAut W) (hρ : ∀ g : P, ρ g = 1 → g = 1)
    (hnc : ¬ ∀ a b : P, a * b = b * a) : f ^ p ≤ Nat.card W := by
  haveI : Fact f.Prime := ⟨hf⟩
  haveI : Fact p.Prime := ⟨hp⟩
  have hWp : IsPGroup f W := fun g => ⟨1, by simpa using hpow g⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hWp
  obtain ⟨e⟩ := CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary hcomm hpow hn
  let φ : MulAut W ≃* GL (Fin n) (ZMod f) := CFSG.SectionRank.Ccomm.elemAutEquivGL e
  let toEnd : GL (Fin n) (ZMod f) →* Module.End (ZMod f) (Fin n → ZMod f) :=
    (Matrix.toLinAlgEquiv' (R := ZMod f) (n := Fin n)).toAlgHom.toMonoidHom.comp
      (Units.coeHom (Matrix (Fin n) (Fin n) (ZMod f)))
  have htoEnd : ∀ u, toEnd u = 1 → u = 1 := fun u h => by
    apply Units.ext
    have h1 : (Matrix.toLinAlgEquiv' (R := ZMod f) (n := Fin n)) (u : Matrix (Fin n) (Fin n)
        (ZMod f)) = (Matrix.toLinAlgEquiv' (R := ZMod f) (n := Fin n)) 1 := by
      rw [map_one]
      exact h
    simpa using (Matrix.toLinAlgEquiv' (R := ZMod f) (n := Fin n)).injective h1
  let ρV : P →* Module.End (ZMod f) (Fin n → ZMod f) := toEnd.comp (φ.toMonoidHom.comp ρ)
  have hfaith : ∀ g, ρV g = 1 → g = 1 := fun g h =>
    hρ g (φ.injective (htoEnd _ h |>.trans (map_one φ).symm))
  have key := finrank_ge_of_faithful_nonabelian (V := Fin n → ZMod f) hfp hP ρV hfaith hnc
  rw [Module.finrank_fin_fun] at key
  rw [hn]
  exact Nat.pow_le_pow_right hf.pos key

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.RankP
