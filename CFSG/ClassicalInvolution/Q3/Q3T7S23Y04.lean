module

public import CFSG.ClassicalInvolution.Q3.Q3T7S23Y03
public import CFSG.ClassicalInvolution.Q3.Q3T7S23A02
public import CFSG.ClassicalInvolution.Q3.Q3T7Q2214

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T7S23

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77
open scoped commutatorElement MatrixGroups


section Commutes

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K K' W : Subgroup G}
  {z u e g : G}

theorem twins_commute_of_exact (hs : Q3T8.Asc77.Hyp23Setting Ω K K' z) (hex : ExactMembers Ω) :
    Commutes K K' := by
  have hst := hs.stand
  have hKΩ : K ∈ Ω := hst.mem
  have d := Q3T8.Asc77.ExactD.TwinPair.of_twinSet hst.hyp hKΩ hs.hz hs.hK' hs.hne.symm
  have h := d.comm_le
  rw [oddCoreOf_eq_bot_of_exact hex hKΩ, bot_inf_eq, le_bot_iff] at h
  intro x hx y hy
  have : ⁅x, y⁆ ∈ ⁅K, K'⁆ := Subgroup.commutator_mem_commutator hx hy
  rw [h, Subgroup.mem_bot] at this
  exact commutatorElement_eq_one_iff_mul_comm.mp this

theorem commutes_of_pow3_centralizer (hs : Q3T8.Asc77.Hyp23Setting Ω K K' z)
    (hd : Q3T8.Asc77.Hyp23bData Ω K K' W z u e g) (hex : ExactMembers Ω) {L : Subgroup G}
    (hLz : L ≤ Subgroup.centralizer ({z} : Set G))
    (hLu : L ≤ Subgroup.centralizer ({u} : Set G)) (hL : Q3W.Pow3 L) : Commutes K L := by
  classical
  have hst := hs.stand
  have hΩ : Q3T7M.HM Ω := hst.modU
  have hKΩ : K ∈ Ω := hst.mem
  have hK'Ω : K' ∈ Ω := hs.hK'.1
  have hzK' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hs.hz hs.hK'
  have hodd : Odd (Nat.card (ZMod 3)) := by
    rw [Nat.card_zmod]
    decide
  obtain ⟨zK, hzK⟩ := hΩ.classical K hKΩ
  obtain ⟨eK⟩ := (hzK.toQ3 (by norm_num)).nonempty_equiv_sl2 (hex K hKΩ)
  obtain ⟨R, R', a, b, r, hR, hR', -, hRN, hR'N, haR, hbR', -, -, hu, haa, hbb, -, -⟩ :=
    Q3T8.Asc77.T7K.exists_decomp hs hd
  have haK : a ∈ K := hR.1 haR
  have hbK' : b ∈ K' := hR'.1 hbR'
  have hcomm : Commutes K K' := twins_commute_of_exact hs hex
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
      ⟨hΩ.conjInvariant ℓ K hKΩ, z, hs.hz, hℓz ▸ hs.hz.conj ℓ⟩
    have h2 : conjSub ℓ K' ∈ twinSet Ω K :=
      ⟨hΩ.conjInvariant ℓ K' hK'Ω, z, hs.hz, hℓz ▸ hzK'.conj ℓ⟩
    rw [hs.twinSet_eq] at h1 h2
    have hne : conjSub ℓ K ≠ conjSub ℓ K' := fun h => hs.hne (conjSub_injective ℓ h).symm
    rcases Set.mem_insert_iff.mp h1 with h1 | h1 <;> rcases Set.mem_insert_iff.mp h2 with h2 | h2
    · exact absurd (h1.trans h2.symm) hne
    · exact Or.inl ⟨h1, Set.mem_singleton_iff.mp h2⟩
    · exact Or.inr ⟨Set.mem_singleton_iff.mp h1, h2⟩
    · exact absurd ((Set.mem_singleton_iff.mp h1).trans (Set.mem_singleton_iff.mp h2).symm) hne
  have hfixK : ∀ w ∈ L, conjSub w K = K ∧ conjSub w K' = K' :=
    fix_of_pow3_two (fun w S => conjSub w S) (fun x y S => conjSub_mul x y S)
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
    rcases T7Z.eq_one_or_eq_of_mem_center hodd eK hz2 hcc with h | h
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
    (fix_of_pow3_two (fun w s => w * s * w⁻¹) (fun x y s => by group) (fun s => by simp) hL
      hmap w hw).1
  let ψ : ↥L →* MulAut ↥K := K.normalizerMonoidHom.comp (Subgroup.inclusion hLN)
  have hψ : ∀ (ℓ : ↥L) (k : ↥K), ((ψ ℓ k : ↥K) : G) = (ℓ : G) * k * (ℓ : G)⁻¹ := fun ℓ k => rfl
  have haa' : (⟨a, haK⟩ : ↥K) * ⟨a, haK⟩ = ⟨z, hs.hz.mem⟩ := Subtype.ext haa
  have hcent : ∀ ℓ : ↥L, ∃ q : ↥K, ψ ℓ = MulAut.conj q ∧
      q * (⟨a, haK⟩ : ↥K) = (⟨a, haK⟩ : ↥K) * q := by
    intro ℓ
    obtain ⟨q, hq⟩ := exists_inner_of_pow3 eK hL ψ ℓ
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
        (T7Z.commute_of_centralizes_sq hodd eK hz2 haa' hq₁ hq₂)
    rw [map_commutatorElement, h₁, h₂, ← map_commutatorElement, hq, map_one]
  have hψ1 : ∀ ℓ : ↥L, ψ ℓ = 1 := by
    intro ℓ
    obtain ⟨q, hq, hqa⟩ := hcent ℓ
    have hqq : ∀ k : ↥K, q * q * k = k * (q * q) := by
      intro k
      have hea : eK ⟨a, haK⟩ * eK ⟨a, haK⟩ = -1 := by
        have hz' : eK ⟨z, hs.hz.mem⟩ = -1 := by
          have := (orderOf_eq_two_iff_of_equiv_sl2 hodd eK ⟨z, hs.hz.mem⟩).mp hz2
          rw [this, MulEquiv.apply_symm_apply]
        rw [← map_mul, haa', hz']
      have hcase := sl2Three_sq_cases (eK ⟨a, haK⟩) (eK q) hea (by
        rw [← map_mul, ← map_mul, hqa])
      apply eK.injective
      simp only [map_mul]
      rcases hcase with h | h
      · rw [h]
        simp
      · rw [h]
        simp
    have hsq : ψ ℓ * ψ ℓ = 1 := by
      rw [hq, ← map_mul]
      refine MulEquiv.ext fun k => ?_
      simp only [MulAut.conj_apply, MulAut.one_apply]
      calc q * q * k * (q * q)⁻¹ = k * (q * q) * (q * q)⁻¹ := by rw [hqq k]
        _ = k := by group
    have h3 := pow3_mem_ker hL ψ hker ℓ
    calc ψ ℓ = ψ ℓ ^ 3 * (ψ ℓ * ψ ℓ)⁻¹ := by group
      _ = 1 := by rw [h3, hsq]; simp
  intro x hx y hy
  have h := congrArg (fun φ : MulAut ↥K => ((φ ⟨x, hx⟩ : ↥K) : G)) (hψ1 ⟨y, hy⟩)
  simp only [hψ, MulAut.one_apply] at h
  calc x * y = (y * x * y⁻¹) * y := by rw [h]
    _ = y * x := by group

end Commutes

end CFSG.ClassicalInvolution.Q3.Q3T7S23
