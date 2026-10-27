module

public import CFSG.ClassicalInvolution.Asc77.AscT7Z5
public import CFSG.ClassicalInvolution.Asc77.AscT7Z13
public import CFSG.ClassicalInvolution.GenericLocal.SL2Automorphisms
public import CFSG.ClassicalInvolution.Asc77.AscT7K6

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open scoped commutatorElement

namespace T7Z

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {K K' W : Subgroup G} {z u e g : G}


theorem commutes_of_perfect_centralizer (hs : Hyp23Setting p f Ω K K' z)
    (hd : Hyp23bData Ω K K' W z u e g) (hex : ExactMembers Ω) {L : Subgroup G}
    (hLz : L ≤ Subgroup.centralizer ({z} : Set G))
    (hLu : L ≤ Subgroup.centralizer ({u} : Set G)) (hL : L ≤ ⁅L, L⁆) : Commutes K L := by
  classical
  have hst := hs.stand
  have hp2 : p ≠ 2 := hst.odd
  have hq : 5 ≤ p ^ f := hst.five
  have hKΩ : K ∈ Ω := hst.mem
  have hK'Ω : K' ∈ Ω := hs.hK'.1
  have hzK' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hs.hz hs.hK'
  have hf : f ≠ 0 := by
    rintro rfl
    simp at hq
  have hcard : Nat.card (GaloisField p f) = p ^ f := GaloisField.card p f hf
  have hodd : Odd (Nat.card (GaloisField p f)) := by
    rw [hcard]
    rcases (Fact.out : p.Prime).eq_two_or_odd' with h | h
    · exact absurd h hp2
    · exact h.pow
  have h4 : 4 ≤ Nat.card (GaloisField p f) := by
    rw [hcard]
    omega
  obtain ⟨zK, hzK⟩ := hst.hyp.classical K hKΩ
  obtain ⟨eK⟩ := hzK.nonempty_equiv_sl2 (hex K hKΩ)
  obtain ⟨R, R', a, b, r, hR, hR', -, hRN, hR'N, haR, hbR', -, -, hu, haa, hbb, -, -⟩ :=
    T7K.exists_decomp hs hd
  have haK : a ∈ K := hR.1 haR
  have hbK' : b ∈ K' := hR'.1 hbR'
  have hcomm := twin_commutes hs hex
  have hz2 : orderOf (⟨z, hs.hz.mem⟩ : ↥K) = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · apply Subtype.ext
      simpa [pow_two] using hs.hz.sq
    · intro h
      exact hs.hz.ne_one (congrArg Subtype.val h)
  have hdich : ∀ ℓ ∈ L, (conjSub ℓ K = K ∧ conjSub ℓ K' = K') ∨
      (conjSub ℓ K = K' ∧ conjSub ℓ K' = K) := by
    intro ℓ hℓ
    have hℓz : ℓ * z * ℓ⁻¹ = z := by
      have := Subgroup.mem_centralizer_singleton_iff.mp (hLz hℓ)
      calc ℓ * z * ℓ⁻¹ = z * ℓ * ℓ⁻¹ := by rw [this]
        _ = z := by group
    have h1 : conjSub ℓ K ∈ twinSet Ω K :=
      ⟨hst.hyp.conjInvariant ℓ K hKΩ, z, hs.hz, hℓz ▸ hs.hz.conj ℓ⟩
    have h2 : conjSub ℓ K' ∈ twinSet Ω K :=
      ⟨hst.hyp.conjInvariant ℓ K' hK'Ω, z, hs.hz, hℓz ▸ hzK'.conj ℓ⟩
    rw [hs.twinSet_eq] at h1 h2
    have hne : conjSub ℓ K ≠ conjSub ℓ K' := fun h => hs.hne (conjSub_injective ℓ h).symm
    rcases Set.mem_insert_iff.mp h1 with h1 | h1 <;> rcases Set.mem_insert_iff.mp h2 with h2 | h2
    · exact absurd (h1.trans h2.symm) hne
    · exact Or.inl ⟨h1, Set.mem_singleton_iff.mp h2⟩
    · exact Or.inr ⟨Set.mem_singleton_iff.mp h1, h2⟩
    · exact absurd ((Set.mem_singleton_iff.mp h1).trans (Set.mem_singleton_iff.mp h2).symm) hne
  have hfixK : ∀ w ∈ L, conjSub w K = K ∧ conjSub w K' = K' :=
    fix_of_perfect_two (fun w S => conjSub w S) (fun x y S => conjSub_mul x y S)
      (fun S => conjSub_one S) hL hdich
  have hLN : L ≤ Subgroup.normalizer (K : Set G) := by
    intro w hw
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      have := conj_mem_conjSub (n := w) hh
      rwa [(hfixK w hw).1] at this
    · intro hh
      have hh' : w * h * w⁻¹ ∈ conjSub w K := by rwa [(hfixK w hw).1]
      rw [mem_conjSub_iff] at hh'
      have e1 : w⁻¹ * (w * h * w⁻¹) * w = h := by group
      rwa [e1] at hh'
  have hmap : ∀ ℓ ∈ L, (ℓ * a * ℓ⁻¹ = a ∧ ℓ * a⁻¹ * ℓ⁻¹ = a⁻¹) ∨
      (ℓ * a * ℓ⁻¹ = a⁻¹ ∧ ℓ * a⁻¹ * ℓ⁻¹ = a) := by
    intro ℓ hℓ
    have ha' : ℓ * a * ℓ⁻¹ ∈ K := by
      have := conj_mem_conjSub (n := ℓ) haK
      rwa [(hfixK ℓ hℓ).1] at this
    have hb' : ℓ * b * ℓ⁻¹ ∈ K' := by
      have := conj_mem_conjSub (n := ℓ) hbK'
      rwa [(hfixK ℓ hℓ).2] at this
    have hℓu : ℓ * u * ℓ⁻¹ = u := by
      have := Subgroup.mem_centralizer_singleton_iff.mp (hLu hℓ)
      calc ℓ * u * ℓ⁻¹ = u * ℓ * ℓ⁻¹ := by rw [this]
        _ = u := by group
    have hab : (ℓ * a * ℓ⁻¹) * (ℓ * b * ℓ⁻¹) = a * b := by
      calc (ℓ * a * ℓ⁻¹) * (ℓ * b * ℓ⁻¹) = ℓ * (a * b) * ℓ⁻¹ := by group
        _ = ℓ * u * ℓ⁻¹ := by rw [hu]
        _ = a * b := by rw [hℓu, hu]
    have hc : a⁻¹ * (ℓ * a * ℓ⁻¹) = b * (ℓ * b * ℓ⁻¹)⁻¹ := by
      calc a⁻¹ * (ℓ * a * ℓ⁻¹) = a⁻¹ * ((ℓ * a * ℓ⁻¹) * (ℓ * b * ℓ⁻¹)) * (ℓ * b * ℓ⁻¹)⁻¹ := by
            group
        _ = a⁻¹ * (a * b) * (ℓ * b * ℓ⁻¹)⁻¹ := by rw [hab]
        _ = b * (ℓ * b * ℓ⁻¹)⁻¹ := by group
    have hcK : a⁻¹ * (ℓ * a * ℓ⁻¹) ∈ K := K.mul_mem (K.inv_mem haK) ha'
    have hcK' : a⁻¹ * (ℓ * a * ℓ⁻¹) ∈ K' := by
      rw [hc]
      exact K'.mul_mem hbK' (K'.inv_mem hb')
    have hcc : (⟨a⁻¹ * (ℓ * a * ℓ⁻¹), hcK⟩ : ↥K) ∈ Subgroup.center ↥K := by
      rw [Subgroup.mem_center_iff]
      intro k
      apply Subtype.ext
      exact hcomm (k : G) k.2 _ hcK'
    have haz : a * z = a⁻¹ := by
      apply eq_inv_of_mul_eq_one_right
      calc a * (a * z) = (a * a) * z := by group
        _ = z * z := by rw [haa]
        _ = 1 := hs.hz.sq
    rcases eq_one_or_eq_of_mem_center hodd eK hz2 hcc with h | h
    · left
      have h' : a⁻¹ * (ℓ * a * ℓ⁻¹) = 1 := congrArg Subtype.val h
      have h'' : ℓ * a * ℓ⁻¹ = a := (inv_mul_eq_one.mp h').symm
      refine ⟨h'', ?_⟩
      calc ℓ * a⁻¹ * ℓ⁻¹ = (ℓ * a * ℓ⁻¹)⁻¹ := by group
        _ = a⁻¹ := by rw [h'']
    · right
      have h' : a⁻¹ * (ℓ * a * ℓ⁻¹) = z := congrArg Subtype.val h
      have h'' : ℓ * a * ℓ⁻¹ = a⁻¹ := by
        calc ℓ * a * ℓ⁻¹ = a * (a⁻¹ * (ℓ * a * ℓ⁻¹)) := by group
          _ = a * z := by rw [h']
          _ = a⁻¹ := haz
      refine ⟨h'', ?_⟩
      calc ℓ * a⁻¹ * ℓ⁻¹ = (ℓ * a * ℓ⁻¹)⁻¹ := by group
        _ = a := by rw [h'', inv_inv]
  have hLa : ∀ w ∈ L, w * a * w⁻¹ = a := fun w hw =>
    (fix_of_perfect_two (fun w s => w * s * w⁻¹) (fun x y s => by group) (fun s => by simp) hL
      hmap w hw).1
  have hperf : Group.IsPerfect ↥L :=
    Subgroup.isPerfect_iff.mpr (le_antisymm (Subgroup.commutator_le.mpr fun x hx y hy => by
      rw [commutatorElement_def]
      exact L.mul_mem (L.mul_mem (L.mul_mem hx hy) (L.inv_mem hx)) (L.inv_mem hy)) hL)
  let ψ : ↥L →* MulAut ↥K := K.normalizerMonoidHom.comp (Subgroup.inclusion hLN)
  have hψ : ∀ (ℓ : ↥L) (k : ↥K), ((ψ ℓ k : ↥K) : G) = (ℓ : G) * k * (ℓ : G)⁻¹ := fun ℓ k => rfl
  have haa' : (⟨a, haK⟩ : ↥K) * ⟨a, haK⟩ = ⟨z, hs.hz.mem⟩ := Subtype.ext haa
  have hcent : ∀ ℓ : ↥L, ∃ q : ↥K, ψ ℓ = MulAut.conj q ∧
      q * (⟨a, haK⟩ : ↥K) = (⟨a, haK⟩ : ↥K) * q := by
    intro ℓ
    obtain ⟨q, hq⟩ := perfect_action_inner_of_equiv_sl2 h4 eK ψ ℓ
    refine ⟨q, hq, ?_⟩
    have h1 : (ψ ℓ (⟨a, haK⟩ : ↥K) : ↥K) = ⟨a, haK⟩ := by
      apply Subtype.ext
      rw [hψ]
      exact hLa ℓ ℓ.2
    rw [hq] at h1
    simp only [MulAut.conj_apply] at h1
    exact mul_inv_eq_iff_eq_mul.mp h1
  have hker : ∀ ℓ m : ↥L, ψ ⁅ℓ, m⁆ = 1 := by
    intro ℓ m
    obtain ⟨q₁, h₁, hq₁⟩ := hcent ℓ
    obtain ⟨q₂, h₂, hq₂⟩ := hcent m
    have hq : ⁅q₁, q₂⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.mpr
        (commute_of_centralizes_sq hodd eK hz2 haa' hq₁ hq₂)
    rw [map_commutatorElement, h₁, h₂, ← map_commutatorElement, hq, map_one]
  have hψ1 : ∀ ℓ : ↥L, ψ ℓ = 1 := by
    have htop : commutator ↥L ≤ ψ.ker := by
      rw [commutator, Subgroup.commutator_le]
      intro ℓ _ m _
      exact hker ℓ m
    have := hperf.commutator_eq_top
    rw [this] at htop
    intro ℓ
    exact htop (Subgroup.mem_top ℓ)
  intro x hx y hy
  have h := congrArg (fun φ : MulAut ↥K => ((φ ⟨x, hx⟩ : ↥K) : G)) (hψ1 ⟨y, hy⟩)
  simp only [hψ, MulAut.one_apply] at h
  calc x * y = (y * x * y⁻¹) * y := by rw [h]
    _ = y * x := by group

end T7Z

end CFSG.ClassicalInvolution.Asc77
