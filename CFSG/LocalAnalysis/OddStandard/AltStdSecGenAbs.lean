module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecGenAut
public import CFSG.LocalAnalysis.OddStandard.AltStdSecStdAlt

public section

namespace CFSG.OddStandard.AltStdSec

open Subgroup Equiv

section Abs

variable {X : Type*} [Group X]

theorem le_of_centralizes {K K' P : Subgroup X} (hP : ⁅P, P⁆ = P)
    (hKK' : ∀ a ∈ K, ∀ b ∈ K', a * b = b * a)
    (hZ : ∀ a b : X, (∀ k ∈ K, a * k = k * a) → (∀ k ∈ K', a * k = k * a) →
      (∀ k ∈ K, b * k = k * b) → (∀ k ∈ K', b * k = k * b) → a * b = b * a)
    (κ' : ↥P →* ↥K')
    (hκ' : ∀ (p : ↥P) (k : ↥K'), (p : X) * (k : X) * (p : X)⁻¹ =
      (κ' p : X) * (k : X) * (κ' p : X)⁻¹)
    (hcent : ∀ p ∈ P, ∀ k ∈ K, p * k = k * p) : P ≤ K' := by
  have hK' : ∀ p : ↥P, ∀ k ∈ K', (p : X) * (κ' p : X)⁻¹ * k = k * ((p : X) * (κ' p : X)⁻¹) := by
    intro p k hk
    have h1 : (κ' p : X)⁻¹ * k * (κ' p : X) ∈ K' := by
      have := K'.mul_mem (K'.mul_mem (K'.inv_mem (κ' p).2) hk) (κ' p).2
      exact this
    have h2 := hκ' p ⟨_, h1⟩
    simp only at h2
    calc (p : X) * (κ' p : X)⁻¹ * k
        = ((p : X) * ((κ' p : X)⁻¹ * k * (κ' p : X)) * (p : X)⁻¹) * ((p : X) * (κ' p : X)⁻¹) := by
          group
      _ = ((κ' p : X) * ((κ' p : X)⁻¹ * k * (κ' p : X)) * (κ' p : X)⁻¹) *
            ((p : X) * (κ' p : X)⁻¹) := by rw [h2]
      _ = k * ((p : X) * (κ' p : X)⁻¹) := by group
  have hK : ∀ p : ↥P, ∀ k ∈ K, (p : X) * (κ' p : X)⁻¹ * k = k * ((p : X) * (κ' p : X)⁻¹) := by
    intro p k hk
    have h1 : (κ' p : X)⁻¹ * k = k * (κ' p : X)⁻¹ := by
      have := hKK' k hk (κ' p : X)⁻¹ (K'.inv_mem (κ' p).2)
      exact this.symm
    calc (p : X) * (κ' p : X)⁻¹ * k = (p : X) * (k * (κ' p : X)⁻¹) := by rw [mul_assoc, h1]
      _ = ((p : X) * k) * (κ' p : X)⁻¹ := by group
      _ = (k * (p : X)) * (κ' p : X)⁻¹ := by rw [hcent p p.2 k hk]
      _ = k * ((p : X) * (κ' p : X)⁻¹) := by group
  let U : ↥P →* X := MonoidHom.mk' (fun p => (p : X) * (κ' p : X)⁻¹) (fun a b => by
    have h1 := hK' b (κ' a : X)⁻¹ (K'.inv_mem (κ' a).2)
    show ((a * b : ↥P) : X) * (κ' (a * b) : X)⁻¹ =
      ((a : X) * (κ' a : X)⁻¹) * ((b : X) * (κ' b : X)⁻¹)
    rw [map_mul]
    calc ((a * b : ↥P) : X) * (((κ' a * κ' b : ↥K') : X))⁻¹
        = (a : X) * (((b : X) * (κ' b : X)⁻¹) * (κ' a : X)⁻¹) := by
          simp only [Subgroup.coe_mul, mul_inv_rev]; group
      _ = (a : X) * ((κ' a : X)⁻¹ * ((b : X) * (κ' b : X)⁻¹)) := by rw [← h1]
      _ = ((a : X) * (κ' a : X)⁻¹) * ((b : X) * (κ' b : X)⁻¹) := by group)
  have hU : ∀ p : ↥P, U p = (p : X) * (κ' p : X)⁻¹ := fun p => rfl
  have hperf : Group.IsPerfect ↥P := Subgroup.isPerfect_iff.2 hP
  have hker : (⊤ : Subgroup ↥P) ≤ U.ker := by
    refine le_of_comm_mem (Q := ⊤) (C := U.ker) ?_ (fun a _ b _ => ?_)
    · rw [← commutator_def]; exact hperf.commutator_eq_top
    · rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv]
      have hc := hZ (U a) (U b) (fun k hk => by rw [hU]; exact hK a k hk)
        (fun k hk => by rw [hU]; exact hK' a k hk) (fun k hk => by rw [hU]; exact hK b k hk)
        (fun k hk => by rw [hU]; exact hK' b k hk)
      rw [hc]; group
  intro p hp
  have h1 : U ⟨p, hp⟩ = 1 := MonoidHom.mem_ker.1 (hker (Subgroup.mem_top _))
  rw [hU] at h1
  have h2 : p = (κ' ⟨p, hp⟩ : X) := mul_inv_eq_one.1 h1
  rw [h2]
  exact (κ' ⟨p, hp⟩).2

theorem hom_trivial_of_not_injective {G M : Type*} [Group G] [Group M] [IsSimpleGroup G]
    (f : G →* M) (hf : ¬ Function.Injective f) (g : G) : f g = 1 := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal f.ker with h | h
  · exact absurd ((MonoidHom.ker_eq_bot_iff f).1 h) hf
  · have : g ∈ f.ker := by rw [h]; exact Subgroup.mem_top g
    exact this

theorem perfect_le_or_le [Finite X] {K K' P : Subgroup X} {z : X} {m k : ℕ} (hm6 : m ≠ 6)
    (hk6 : 5 ≤ k) (hkm : k ≤ m) (hmk : m ≤ k + 3)
    (eK : ↥K ≃* alternatingGroup (Fin m)) (eK' : ↥K' ≃* alternatingGroup (Fin m))
    (eP : ↥P ≃* alternatingGroup (Fin k)) (hz : z * z = 1)
    (hKz : ∀ x ∈ K, z * x * z⁻¹ ∈ K') (hK'z : ∀ x ∈ K', z * x * z⁻¹ ∈ K)
    (hKK' : ∀ a ∈ K, ∀ b ∈ K', a * b = b * a)
    (hZ : ∀ a b : X, (∀ k ∈ K, a * k = k * a) → (∀ k ∈ K', a * k = k * a) →
      (∀ k ∈ K, b * k = k * b) → (∀ k ∈ K', b * k = k * b) → a * b = b * a)
    (hNK : ∀ p ∈ P, ∀ x ∈ K, p * x * p⁻¹ ∈ K) (hNK' : ∀ p ∈ P, ∀ x ∈ K', p * x * p⁻¹ ∈ K')
    (hPP : ∀ a ∈ P, ∀ b ∈ P, a * (z * b * z⁻¹) = (z * b * z⁻¹) * a) :
    P ≤ K ∨ P ≤ K' := by
  have hm5 : 5 ≤ m := by omega
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz
  have hPsimple : IsSimpleGroup ↥P := isSimpleGroup_of_alt (by omega) eP
  have hPperf : ⁅P, P⁆ = P := Subgroup.isPerfect_iff.1 ⟨(isQuasisimple_of_alt (by omega) eP).1⟩
  obtain ⟨κ, hκ⟩ := exists_inner_hom hm5 hm6 eK hPperf hNK
  obtain ⟨κ', hκ'⟩ := exists_inner_hom hm5 hm6 eK' hPperf hNK'
  let w : ↥P →* ↥K := MonoidHom.mk' (fun q => (⟨z * (κ' q : X) * z⁻¹, hK'z _ (κ' q).2⟩ : ↥K))
    (fun a b => by
      apply Subtype.ext
      show z * ((κ' (a * b) : ↥K') : X) * z⁻¹ = (z * (κ' a : X) * z⁻¹) * (z * (κ' b : X) * z⁻¹)
      rw [map_mul, Subgroup.coe_mul]
      group)
  have hw : ∀ q : ↥P, ((w q : ↥K) : X) = z * (κ' q : X) * z⁻¹ := fun q => rfl
  have hact : ∀ (q : ↥P) (x : ↥K), z * (q : X) * z⁻¹ * (x : X) * (z * (q : X) * z⁻¹)⁻¹ =
      (w q : X) * (x : X) * (w q : X)⁻¹ := by
    intro q x
    have hx1 : z⁻¹ * (x : X) * z ∈ K' := by
      have := hKz (x : X) x.2
      rw [hzi] at this ⊢
      exact this
    have h1 := hκ' q ⟨_, hx1⟩
    simp only at h1
    rw [hw]
    calc z * (q : X) * z⁻¹ * (x : X) * (z * (q : X) * z⁻¹)⁻¹
        = z * ((q : X) * (z⁻¹ * (x : X) * z) * (q : X)⁻¹) * z⁻¹ := by group
      _ = z * ((κ' q : X) * (z⁻¹ * (x : X) * z) * (κ' q : X)⁻¹) * z⁻¹ := by rw [h1]
      _ = z * (κ' q : X) * z⁻¹ * (x : X) * (z * (κ' q : X) * z⁻¹)⁻¹ := by group
  have hcomm : ∀ p q : ↥P, (κ p : X) * (w q : X) = (w q : X) * (κ p : X) := by
    intro p q
    set a : ↥K := κ p with ha
    set b : ↥K := w q with hb
    have hkey : ∀ g : ↥K, a * (b * g * b⁻¹) * a⁻¹ = b * (a * g * a⁻¹) * b⁻¹ := by
      intro g
      apply Subtype.ext
      set y : X := z * (q : X) * z⁻¹ with hy
      have e1 : (p : X) * y = y * (p : X) := hPP p p.2 q q.2
      have h1 : ∀ x : X, (p : X) * (y * x * y⁻¹) * (p : X)⁻¹ =
          y * ((p : X) * x * (p : X)⁻¹) * y⁻¹ := by
        intro x
        calc (p : X) * (y * x * y⁻¹) * (p : X)⁻¹ = ((p : X) * y) * x * ((p : X) * y)⁻¹ := by group
          _ = (y * (p : X)) * x * (y * (p : X))⁻¹ := by rw [e1]
          _ = y * ((p : X) * x * (p : X)⁻¹) * y⁻¹ := by group
      have hA : (p : X) * ((b * g * b⁻¹ : ↥K) : X) * (p : X)⁻¹ =
          ((a * (b * g * b⁻¹) * a⁻¹ : ↥K) : X) := hκ p _
      have hB : y * ((a * g * a⁻¹ : ↥K) : X) * y⁻¹ = ((b * (a * g * a⁻¹) * b⁻¹ : ↥K) : X) :=
        hact q _
      have hC : y * (g : X) * y⁻¹ = ((b * g * b⁻¹ : ↥K) : X) := hact q g
      have hD : (p : X) * (g : X) * (p : X)⁻¹ = ((a * g * a⁻¹ : ↥K) : X) := hκ p g
      calc ((a * (b * g * b⁻¹) * a⁻¹ : ↥K) : X)
          = (p : X) * ((b * g * b⁻¹ : ↥K) : X) * (p : X)⁻¹ := hA.symm
        _ = (p : X) * (y * (g : X) * y⁻¹) * (p : X)⁻¹ := by rw [hC]
        _ = y * ((p : X) * (g : X) * (p : X)⁻¹) * y⁻¹ := h1 _
        _ = y * ((a * g * a⁻¹ : ↥K) : X) * y⁻¹ := by rw [hD]
        _ = ((b * (a * g * a⁻¹) * b⁻¹ : ↥K) : X) := hB
    have hu : a⁻¹ * b⁻¹ * a * b ∈ Subgroup.center ↥K := by
      rw [Subgroup.mem_center_iff]
      intro g
      have h := hkey g
      calc g * (a⁻¹ * b⁻¹ * a * b)
          = (a⁻¹ * b⁻¹ * (b * (a * g * a⁻¹) * b⁻¹)) * (a * b) := by group
        _ = (a⁻¹ * b⁻¹ * (a * (b * g * b⁻¹) * a⁻¹)) * (a * b) := by rw [h]
        _ = (a⁻¹ * b⁻¹ * a * b) * g := by group
    rw [center_eq_bot_of_alt (by omega) eK] at hu
    have hu1 : a⁻¹ * b⁻¹ * a * b = 1 := hu
    have : a * b = b * a := by
      calc a * b = (b * a) * (a⁻¹ * b⁻¹ * a * b) := by group
        _ = b * a := by rw [hu1, mul_one]
    exact congrArg Subtype.val this
  by_cases h1 : Function.Injective κ
  · by_cases h2 : Function.Injective w
    · exfalso
      have hc : ∀ (p q : ↥P), Commute (κ p) (w q) := fun p q => Subtype.ext (hcomm p q)
      let F : ↥P × ↥P →* ↥K := κ.noncommCoprod w hc
      have hF : ∀ pq : ↥P × ↥P, F pq = κ pq.1 * w pq.2 := fun pq => rfl
      have hFinj : Function.Injective F := by
        rw [injective_iff_map_eq_one]
        rintro ⟨p, q⟩ hpq
        rw [hF] at hpq
        simp only at hpq
        have hk : κ p = (w q)⁻¹ := eq_inv_of_mul_eq_one_left hpq
        have hcen : p ∈ Subgroup.center ↥P := by
          rw [Subgroup.mem_center_iff]
          intro g
          apply h1
          show κ (g * p) = κ (p * g)
          rw [map_mul, map_mul, hk, ← map_inv]
          exact (Subtype.ext (hcomm g q⁻¹))
        rw [center_eq_bot_of_alt (by omega) eP] at hcen
        have hp : p = 1 := hcen
        subst hp
        have hq : w q = 1 := by simpa using hpq
        have : q = 1 := h2 (hq.trans (map_one w).symm)
        subst this
        rfl
      have hdvd := Subgroup.card_dvd_of_injective F hFinj
      rw [Nat.card_prod, Nat.card_congr eP.toEquiv, Nat.card_congr eK.toEquiv, ← pow_two] at hdvd
      exact not_dvd_sq_card_alt hk6 hkm hmk hdvd
    ·
      left
      have hw1 := hom_trivial_of_not_injective w h2
      have hκ'1 : ∀ p : ↥P, κ' p = 1 := by
        intro p
        have h3 : z * (κ' p : X) * z⁻¹ = 1 := by
          have := congrArg Subtype.val (hw1 p)
          rwa [hw] at this
        have h4 : (κ' p : X) = 1 := by
          have := congrArg (fun x : X => z⁻¹ * x * z) h3
          simpa [mul_assoc] using this
        exact Subtype.ext h4
      refine le_of_centralizes (K := K') (K' := K) hPperf (fun a ha b hb => (hKK' b hb a ha).symm)
        (fun a b h1 h2 h3 h4 => hZ a b h2 h1 h4 h3) κ hκ (fun p hp k hk => ?_)
      have := hκ' ⟨p, hp⟩ ⟨k, hk⟩
      rw [hκ'1] at this
      simp only [OneMemClass.coe_one, one_mul, inv_one, mul_one] at this
      calc p * k = (p * k * p⁻¹) * p := by group
        _ = k * p := by rw [this]
  ·
    right
    have hκ1 := hom_trivial_of_not_injective κ h1
    refine le_of_centralizes (K := K) (K' := K') hPperf hKK' hZ κ' hκ' (fun p hp k hk => ?_)
    have := hκ ⟨p, hp⟩ ⟨k, hk⟩
    rw [hκ1] at this
    simp only [OneMemClass.coe_one, one_mul, inv_one, mul_one] at this
    calc p * k = (p * k * p⁻¹) * p := by group
      _ = k * p := by rw [this]

end Abs

end CFSG.OddStandard.AltStdSec
