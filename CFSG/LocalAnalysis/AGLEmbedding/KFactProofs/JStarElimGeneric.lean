module

public import CFSG.LocalAnalysis.AGLEmbedding.JStarGenericDefs

public section

namespace CFSG.AGLEmbedding

open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

theorem center_bot_of_simple_nonab {G : Type*} [Group G] [IsSimpleGroup G]
    (h : ∃ a b : G, a * b ≠ b * a) : Subgroup.center G = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h' | h'
  · exact h'
  · exfalso
    obtain ⟨a, b, hab⟩ := h
    exact hab (Subgroup.mem_center_iff.mp (h' ▸ Subgroup.mem_top a) b).symm

theorem JStarElimDataOf.card_dvd_card {L₀ L : Type} [Group L₀] [Finite L₀] [Group L] {p B : ℕ}
    [IsSimpleGroup L] (hnc : ∃ a b : L, a * b ≠ b * a) (hOut : Group.IsSolvable (Outer L₀))
    (h : JStarElimDataOf L₀ p B L) : Nat.card L ∣ Nat.card L₀ := by
  obtain ⟨A, J, -, -, -, φ, hφ, -⟩ := h
  let ψ : J →* Outer L₀ := (QuotientGroup.mk' (inner L₀)).comp J.subtype
  have hN : (ψ.ker.map φ).Normal := Subgroup.Normal.map inferInstance φ hφ
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (ψ.ker.map φ) with h0 | h1
  · exfalso
    have hle : ψ.ker ≤ φ.ker := (Subgroup.map_eq_bot_iff ψ.ker).mp h0
    let g : ψ.range →* L :=
      (QuotientGroup.lift ψ.ker φ hle).comp (QuotientGroup.quotientKerEquivRange ψ).symm.toMonoidHom
    have hg : Function.Surjective g :=
      (QuotientGroup.lift_surjective_of_surjective ψ.ker φ hφ hle).comp
        (QuotientGroup.quotientKerEquivRange ψ).symm.surjective
    have hsolv : Group.IsSolvable L := Group.isSolvable_of_surjective hg
    obtain ⟨a, b, hab⟩ := hnc
    exact hab ((IsSimpleGroup.comm_iff_isSolvable.mpr hsolv) a b)
  · have h1' : Nat.card L ∣ Nat.card ψ.ker := by
      have := Subgroup.card_map_dvd (f := φ) ψ.ker
      rwa [h1, Subgroup.card_top] at this
    let I : Subgroup (MulAut L₀) := inner L₀
    let χ : ψ.ker →* I :=
      (J.subtype.comp ψ.ker.subtype).codRestrict I fun x =>
        (QuotientGroup.eq_one_iff (N := I) _).mp (MonoidHom.mem_ker.mp x.2)
    have hχ : Function.Injective χ := by
      intro x y hxy
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : I => (z : MulAut L₀)) hxy
    exact h1'.trans ((Subgroup.card_dvd_of_injective χ hχ).trans (Subgroup.card_range_dvd _))

theorem JStarElimDataOf.pow_dvd_of_center_eq_bot {L₀ L : Type} [Group L₀] [Finite L₀] [Group L]
    {p B : ℕ} [Fact p.Prime] (hZ : Subgroup.center L₀ = ⊥) (h : JStarElimDataOf L₀ p B L) {k : ℕ}
    (hk : p ^ k ∣ Nat.card L₀) : p ^ k ∣ B := by
  obtain ⟨A, -, hInn, -, hpA, -⟩ := h
  obtain ⟨H, hH⟩ := Sylow.exists_subgroup_card_pow_prime p hk
  have hinj : Function.Injective (MulAut.conj : L₀ →* MulAut L₀) := by
    rw [← MonoidHom.ker_eq_bot_iff, ← hZ]
    refine le_antisymm (fun x hx => Subgroup.mem_center_iff.mpr fun g => ?_) ?_
    · have hxg : x * g * x⁻¹ = g := by
        simpa using congrArg (fun f : MulAut L₀ => f g) (MonoidHom.mem_ker.mp hx)
      calc g * x = x * g * x⁻¹ * x := by rw [hxg]
        _ = x * g := by group
    · intro x hx
      rw [MonoidHom.mem_ker]
      ext g
      simp [(Subgroup.mem_center_iff.mp hx g).symm]
  have hcard : Nat.card (H.map (MulAut.conj : L₀ →* MulAut L₀)) = p ^ k := by
    rw [Subgroup.card_map_of_injective hinj, hH]
  have hS := hpA _ ((Subgroup.map_le_range _ _).trans hInn) (IsPGroup.of_card hcard)
  rwa [hcard] at hS

theorem JStarElimDataOf.orderTest {L₀ L : Type} [Group L₀] [Finite L₀] [Group L] {p B : ℕ}
    [Fact p.Prime] [IsSimpleGroup L₀] [IsSimpleGroup L] (hnc₀ : ∃ a b : L₀, a * b ≠ b * a)
    (hnc : ∃ a b : L, a * b ≠ b * a) (hOut : Group.IsSolvable (Outer L₀))
    (h : JStarElimDataOf L₀ p B L) :
    Nat.card L ∣ Nat.card L₀ ∧ ∀ k : ℕ, p ^ k ∣ Nat.card L₀ → p ^ k ∣ B :=
  ⟨h.card_dvd_card hnc hOut, fun _ hk =>
    h.pow_dvd_of_center_eq_bot (center_bot_of_simple_nonab hnc₀) hk⟩

theorem outer_solvable_of_simple_comm {L₀ : Type} [Group L₀] [Finite L₀] [IsSimpleGroup L₀]
    (hab : ∀ a b : L₀, a * b = b * a) : Group.IsSolvable (Outer L₀) := by
  have : IsMulCommutative L₀ := ⟨⟨hab⟩⟩
  have hpr : (Nat.card L₀).Prime := Group.is_simple_iff_prime_card.mp inferInstance
  have : Fact (Nat.card L₀).Prime := ⟨hpr⟩
  have : IsCyclic L₀ := isCyclic_of_prime_card rfl
  have hU : Group.IsSolvable (ZMod (Nat.card L₀))ˣ := Group.isSolvable_of_comm mul_comm
  have h1 : Group.IsSolvable (MulAut L₀) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (IsCyclic.mulAutMulEquiv L₀).toMonoidHom) (IsCyclic.mulAutMulEquiv L₀).injective
  infer_instance

theorem JStarElimDataOf.orderTest_of_schreier {L₀ L : Type} [Group L₀] [Finite L₀] [Group L]
    {p B : ℕ} [Fact p.Prime] [IsSimpleGroup L₀] [IsSimpleGroup L]
    (hnc : ∃ a b : L, a * b ≠ b * a)
    (hOut : (∃ a b : L₀, a * b ≠ b * a) → Group.IsSolvable (Outer L₀))
    (h : JStarElimDataOf L₀ p B L) :
    Nat.card L ∣ Nat.card L₀ ∧ ∀ k : ℕ, p ^ k ∣ Nat.card L₀ → p ^ k ∣ B := by
  by_cases hab : ∃ a b : L₀, a * b ≠ b * a
  · exact h.orderTest hab hnc (hOut hab)
  · exfalso
    push Not at hab
    have hdvd := h.card_dvd_card hnc (outer_solvable_of_simple_comm hab)
    have : IsMulCommutative L₀ := ⟨⟨hab⟩⟩
    have hpr : (Nat.card L₀).Prime := Group.is_simple_iff_prime_card.mp inferInstance
    obtain ⟨a, b, hab'⟩ := hnc
    rcases (Nat.dvd_prime hpr).mp hdvd with h1 | h1
    · have : Subsingleton L := (Nat.card_eq_one_iff_unique.mp h1).1
      exact hab' (Subsingleton.elim _ _)
    · have : Fact (Nat.card L).Prime := ⟨h1 ▸ hpr⟩
      have : IsCyclic L := isCyclic_of_prime_card rfl
      exact hab' (IsCyclic.isMulCommutative.is_comm.comm a b)

theorem nonabelian_of_simple_of_sq_dvd {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    {q : ℕ} (hq : q.Prime) (h : q ^ 2 ∣ Nat.card G) : ∃ a b : G, a * b ≠ b * a := by
  by_contra hcomm
  push Not at hcomm
  have : IsMulCommutative G := ⟨⟨hcomm⟩⟩
  have hpr : (Nat.card G).Prime := Group.is_simple_iff_prime_card.mp inferInstance
  rcases hpr.eq_one_or_self_of_dvd q ((dvd_pow_self q two_ne_zero).trans h) with h1 | h1
  · exact hq.one_lt.ne' h1
  · rw [h1] at h
    have h2 := Nat.le_of_dvd hpr.pos h
    have h3 := hpr.two_le
    nlinarith

theorem isCatalogGroup_of_list {p : ℕ} (hp : 2 ≤ p) {L₀ : Type} [Group L₀]
    (h : (∃ d : TauCeti.ValidLieTypeIndex, P1ThreeLieList p d ∧
        Nonempty (L₀ ≃* (TauCeti.CFSGIndex.lie d).Group)) ∨
      Nonempty (L₀ ≃* alternatingGroup (Fin (3 * p))) ∨
      (∃ s : TauCeti.SporadicName, P1ThreeSporList p s ∧
        Nonempty (L₀ ≃* (TauCeti.CFSGIndex.sporadic s).Group))) :
    Open.IsCatalogGroup L₀ := by
  rcases h with ⟨d, -, he⟩ | he | ⟨s, -, he⟩
  · obtain ⟨e⟩ := he
    exact ⟨.lie d, ⟨e⟩⟩
  · obtain ⟨e⟩ := he
    have h5 : 5 ≤ 3 * p := by omega
    exact ⟨.alternating (3 * p) h5, ⟨e⟩⟩
  · obtain ⟨e⟩ := he
    exact ⟨.sporadic s, ⟨e⟩⟩

theorem nat_card_alternatingGroup_three_mul_three :
    Nat.card (alternatingGroup (Fin (3 * 3))) = 181440 := by
  have h2 := two_mul_nat_card_alternatingGroup (α := Fin (3 * 3))
  simp only [Nat.card_perm, Nat.card_fin] at h2
  have h9 : Nat.factorial (3 * 3) = 362880 := by decide
  omega

theorem nat_card_alternatingGroup_three_mul_five :
    Nat.card (alternatingGroup (Fin (3 * 5))) = 653837184000 := by
  have h2 := two_mul_nat_card_alternatingGroup (α := Fin (3 * 5))
  simp only [Nat.card_perm, Nat.card_fin] at h2
  have h15 : Nat.factorial (3 * 5) = 1307674368000 := by decide
  omega

end CFSG.AGLEmbedding
