module

public import CFSG.LargeExtraspecial.S12Five

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions

universe u

@[expose] noncomputable def s12RelCore {X : Type*} [Group X] (p : ℕ) (H : Subgroup X) :
    Subgroup X :=
  sSup {N : Subgroup X | N ≤ H ∧ H ≤ normalizer (N : Set X) ∧ IsPGroup p N}

theorem s12_relCore_spec {X : Type*} [Group X] [Finite X] (p : ℕ) [Fact p.Prime]
    {H K : Subgroup X} (hKH : K ≤ normalizer (H : Set X)) :
    IsPGroup p (s12RelCore p H) ∧ s12RelCore p H ≤ H ∧
      K ≤ normalizer (s12RelCore p H : Set X) ∧
      ∀ N : Subgroup X, N ≤ H → H ≤ normalizer (N : Set X) → IsPGroup p N →
        N ≤ s12RelCore p H := by
  set F := {N : Subgroup X | N ≤ H ∧ H ≤ normalizer (N : Set X) ∧ IsPGroup p N} with hF
  have hbot : (⊥ : Subgroup X) ∈ F := by
    refine ⟨bot_le, fun x _ => ?_, IsPGroup.of_bot⟩
    rw [mem_normalizer_iff]
    intro y
    simp only [mem_bot]
    constructor
    · rintro rfl; group
    · intro h
      calc y = x⁻¹ * (x * y * x⁻¹) * x := by group
        _ = 1 := by rw [h]; group
  have hne : F.Nonempty := ⟨⊥, hbot⟩
  have hdir : DirectedOn (· ≤ ·) F := by
    rintro Q₁ ⟨h1H, h1N, h1p⟩ Q₂ ⟨h2H, h2N, h2p⟩
    exact ⟨Q₁ ⊔ Q₂, ⟨sup_le h1H h2H, s12_le_normalizer_sup h1N h2N,
      IsPGroup.to_sup_of_normal_right' h1p h2p (le_trans h1H h2N)⟩, le_sup_left, le_sup_right⟩
  have hmem : ∀ x, x ∈ s12RelCore p H ↔ ∃ Q ∈ F, x ∈ Q := fun x =>
    Subgroup.mem_sSup_of_directedOn hne hdir
  refine ⟨?_, sSup_le fun Q hQ => hQ.1, ?_, fun N h1 h2 h3 => le_sSup ⟨h1, h2, h3⟩⟩
  · intro x
    obtain ⟨Q, hQ, hxQ⟩ := (hmem x).mp x.2
    obtain ⟨k, hk⟩ := hQ.2.2 ⟨x, hxQ⟩
    exact ⟨k, Subtype.ext (by simpa using congrArg Subtype.val hk)⟩
  · intro k hk
    have hconj : ∀ {k : X}, k ∈ K → ∀ x ∈ s12RelCore p H, k * x * k⁻¹ ∈ s12RelCore p H := by
      intro k hk x hx
      obtain ⟨Q, ⟨hQH, hQN, hQp⟩, hxQ⟩ := (hmem x).mp hx
      refine (hmem _).mpr ⟨Q.map (MulAut.conj k).toMonoidHom, ⟨?_, ?_, hQp.map _⟩,
        ⟨x, hxQ, rfl⟩⟩
      · rintro _ ⟨y, hy, rfl⟩
        exact (mem_normalizer_iff.mp (hKH hk) y).mp (hQH hy)
      · intro h hh
        have hk' : k⁻¹ * h * k ∈ H := by
          have := (mem_normalizer_iff.mp (hKH (K.inv_mem hk)) h).mp hh
          simpa using this
        rw [mem_normalizer_iff]
        intro y
        rw [s12_mem_map_conj_iff, s12_mem_map_conj_iff]
        have e : k⁻¹ * (h * y * h⁻¹) * k =
            (k⁻¹ * h * k) * (k⁻¹ * y * k) * (k⁻¹ * h * k)⁻¹ := by group
        rw [e]
        exact mem_normalizer_iff.mp (hQN hk') _
    rw [mem_normalizer_iff]
    intro x
    exact ⟨hconj hk x, fun hx => by simpa [mul_assoc] using hconj (K.inv_mem hk) _ hx⟩

namespace Setting

variable {G : Type u} [Group G] [Finite G] (S : Setting G)

@[expose] noncomputable def O3Xbar12 (g : G) : Subgroup S.O := s12RelCore 3 (S.Xbar12 g)

@[expose] noncomputable def Z3Xbar12 (g : G) : Subgroup S.O :=
  S.O3Xbar12 g ⊓ centralizer (S.O3Xbar12 g : Set S.O)

variable {S}

instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

theorem O3Xbar12_spec (g : G) :
    IsPGroup 3 (S.O3Xbar12 g) ∧ S.O3Xbar12 g ≤ S.Xbar12 g ∧
      S.Mbar ≤ normalizer (S.O3Xbar12 g : Set S.O) ∧
      ∀ N : Subgroup S.O, N ≤ S.Xbar12 g → S.Xbar12 g ≤ normalizer (N : Set S.O) →
        IsPGroup 3 N → N ≤ S.O3Xbar12 g :=
  s12_relCore_spec 3 Mbar_le_normalizer_Xbar12

theorem Z3Xbar12_le_Mbar {g : G} : S.Z3Xbar12 g ≤ S.Mbar :=
  inf_le_left.trans ((O3Xbar12_spec (S := S) g).2.1.trans Xbar12_le_Mbar)

theorem isPGroup_Z3Xbar12 {g : G} : IsPGroup 3 (S.Z3Xbar12 g) :=
  (O3Xbar12_spec (S := S) g).1.to_le inf_le_left

theorem commute_of_mem_Z3Xbar12 {g : G} {x y : S.O} (hx : x ∈ S.Z3Xbar12 g)
    (hy : y ∈ S.Z3Xbar12 g) : x * y = y * x :=
  (mem_centralizer_iff.mp hx.2 y hy.1).symm

theorem Mbar_le_normalizer_Z3Xbar12 {g : G} : S.Mbar ≤ normalizer (S.Z3Xbar12 g : Set S.O) := by
  intro m hm
  have hO := (O3Xbar12_spec (S := S) g).2.2.1
  refine mem_normalizer_of_conj_le (fun c hc => ⟨?_, ?_⟩) (fun c hc => ⟨?_, ?_⟩)
  · exact (mem_normalizer_iff.mp (hO hm) c).mp hc.1
  · refine mem_centralizer_iff.mpr fun y hy => ?_
    have hy' : m⁻¹ * y * m⁻¹⁻¹ ∈ S.O3Xbar12 g :=
      (mem_normalizer_iff.mp (hO (S.Mbar.inv_mem hm)) y).mp hy
    have e := mem_centralizer_iff.mp hc.2 _ hy'
    calc y * (m * c * m⁻¹) = m * ((m⁻¹ * y * m⁻¹⁻¹) * c) * m⁻¹ := by group
      _ = m * (c * (m⁻¹ * y * m⁻¹⁻¹)) * m⁻¹ := by rw [e]
      _ = m * c * m⁻¹ * y := by group
  · exact (mem_normalizer_iff.mp (hO (S.Mbar.inv_mem hm)) c).mp hc.1
  · refine mem_centralizer_iff.mpr fun y hy => ?_
    have hy' : m * y * m⁻¹ ∈ S.O3Xbar12 g := (mem_normalizer_iff.mp (hO hm) y).mp hy
    have e := mem_centralizer_iff.mp hc.2 _ hy'
    calc y * (m⁻¹ * c * m⁻¹⁻¹) = m⁻¹ * ((m * y * m⁻¹) * c) * m := by group
      _ = m⁻¹ * (c * (m * y * m⁻¹)) * m := by rw [e]
      _ = m⁻¹ * c * m⁻¹⁻¹ * y := by group

theorem Z3Xbar12_ne_bot {g : G} (h : S.O3Xbar12 g ≠ ⊥) : S.Z3Xbar12 g ≠ ⊥ := by
  have hp := (O3Xbar12_spec (S := S) g).1
  have : Nontrivial (S.O3Xbar12 g) := (nontrivial_iff_ne_bot _).mpr h
  have hc := hp.center_nontrivial
  obtain ⟨y, hy1⟩ := exists_ne (1 : center (S.O3Xbar12 g))
  intro hb
  apply hy1
  have hmem : ((y : S.O3Xbar12 g) : S.O) ∈ S.Z3Xbar12 g := by
    refine ⟨(y : S.O3Xbar12 g).2, mem_centralizer_iff.mpr fun x hx => ?_⟩
    have := mem_center_iff.mp y.2 ⟨x, hx⟩
    exact congrArg Subtype.val this
  rw [hb, mem_bot] at hmem
  exact Subtype.ext (Subtype.ext hmem)

end Setting

end CFSG.LargeExtraspecial
