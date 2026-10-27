module

public import CFSG.SignalizerFunctorTheorem.NonLocalExc.Heis
public import CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.HeisRoot

public section

open scoped commutatorElement

namespace CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit

open CFSG.SignalizerFunctorTheorem.NonLocalExc

section Generic

variable {Γ : Type*} [Group Γ] {K : Type} [Field K] {S : Type} [Fintype S] [DecidableEq S]
  (H : HeisSystem Γ K S)

@[expose] def heisZ : Multiplicative K →* Γ where
  toFun c := H.z c.toAdd
  map_one' := H.z_zero
  map_mul' c d := H.z_add c.toAdd d.toAdd

@[expose] def heisXa (s : S) : Multiplicative K →* Γ where
  toFun c := H.xa s c.toAdd
  map_one' := H.xa_zero s
  map_mul' c d := H.xa_add s c.toAdd d.toAdd

@[expose] noncomputable def heisXaProd : Multiplicative (S → K) →* Γ :=
  (MonoidHom.noncommPiCoprod (fun s : S => heisXa H s)
    (by intro s t _ x y; exact H.xa_comm s t x.toAdd y.toAdd)).comp
    (MulEquiv.piMultiplicative (fun _ : S => K)).toMonoidHom

theorem heisXaProd_single (s : S) (d : K) :
    heisXaProd H (Multiplicative.ofAdd (Pi.single s d)) = H.xa s d := by
  have h : (MulEquiv.piMultiplicative (fun _ : S => K)).toMonoidHom
      (Multiplicative.ofAdd (Pi.single s d)) = Pi.mulSingle s (Multiplicative.ofAdd d) := by
    funext j
    by_cases hj : j = s
    · subst hj
      simp [MulEquiv.piMultiplicative]
    · simp [MulEquiv.piMultiplicative, hj]
  rw [heisXaProd, MonoidHom.comp_apply, h, MonoidHom.noncommPiCoprod_mulSingle]
  rfl

@[expose] def heisBeta : (S → K) →ₗ[K] (S → K) →ₗ[K] K :=
  LinearMap.mk₂ K (fun u v => ∑ s, H.ε s * u s * v s)
    (fun u u' v => by simp [mul_add, add_mul, Finset.sum_add_distrib])
    (fun c u v => by
      simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun s _ => by ring)
    (fun u v v' => by simp [mul_add, Finset.sum_add_distrib])
    (fun c u v => by
      simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun s _ => by ring)

omit [DecidableEq S] in
theorem heisBeta_apply (u v : S → K) : heisBeta H u v = ∑ s, H.ε s * u s * v s := rfl

theorem heisBeta_nondeg_right {v : S → K} (hv : v ≠ 0) : ∃ u, heisBeta H u v ≠ 0 := by
  obtain ⟨s, hs0⟩ := Function.ne_iff.1 hv
  have hs : v s ≠ 0 := hs0
  refine ⟨Pi.single s (1 / (H.ε s * v s)), ?_⟩
  rw [heisBeta_apply, Finset.sum_eq_single s]
  · simp only [Pi.single_eq_same]
    have h1 := H.ε_ne s
    have e : H.ε s * (1 / (H.ε s * v s)) * v s = 1 := by field_simp
    rw [e]
    exact one_ne_zero
  · intro j _ hj
    simp [hj]
  · intro h
    exact absurd (Finset.mem_univ s) h

theorem heisBeta_nondeg_left {u : S → K} (hu : u ≠ 0) : ∃ v, heisBeta H u v ≠ 0 := by
  obtain ⟨s, hs0⟩ := Function.ne_iff.1 hu
  have hs : u s ≠ 0 := hs0
  refine ⟨Pi.single s (1 / (H.ε s * u s)), ?_⟩
  rw [heisBeta_apply, Finset.sum_eq_single s]
  · simp only [Pi.single_eq_same]
    have h1 := H.ε_ne s
    have e : H.ε s * u s * (1 / (H.ε s * u s)) = 1 := by field_simp
    rw [e]
    exact one_ne_zero
  · intro j _ hj
    simp [hj]
  · intro h
    exact absurd (Finset.mem_univ s) h

@[expose] noncomputable def heisB (v : S → K) : Γ := (H.yElt v)⁻¹

omit [DecidableEq S] in
theorem heisB_comm_z (c : Multiplicative K) (v : S → K) :
    heisB H v * heisZ H c = heisZ H c * heisB H v :=
  ((Commute.inv_left (H.yElt_comm_z v c.toAdd))).eq

theorem heisZ_comm_xaProd (c : Multiplicative K) (u : Multiplicative (S → K)) :
    heisZ H c * heisXaProd H u = heisXaProd H u * heisZ H c := by
  have hall : ∀ w : S → K, ∀ c' : K, H.z c' * heisXaProd H (Multiplicative.ofAdd w) =
      heisXaProd H (Multiplicative.ofAdd w) * H.z c' := by
    intro w c'
    have hw : w = ∑ s, Pi.single s (w s) := (Finset.univ_sum_single w).symm
    rw [hw]
    refine Finset.sum_induction _ (fun x => H.z c' * heisXaProd H (Multiplicative.ofAdd x) =
        heisXaProd H (Multiplicative.ofAdd x) * H.z c') ?_ ?_ ?_
    · intro x y hx hy
      rw [ofAdd_add, map_mul, ← mul_assoc, hx, mul_assoc, hy, mul_assoc]
    · simp
    · intro s _
      rw [heisXaProd_single]
      exact H.z_comm_a c' s _
  exact hall u.toAdd c.toAdd

theorem heisXaProd_conj (v u : S → K) :
    heisB H v * heisXaProd H (Multiplicative.ofAdd u) * (heisB H v)⁻¹ =
      heisXaProd H (Multiplicative.ofAdd u) * H.z (heisBeta H u v) := by
  have hw : u = ∑ s, Pi.single s (u s) := (Finset.univ_sum_single u).symm
  have key : ∀ x : S → K, heisB H v * heisXaProd H (Multiplicative.ofAdd x) * (heisB H v)⁻¹ =
      heisXaProd H (Multiplicative.ofAdd x) * H.z (heisBeta H x v) := by
    intro x
    have hx : x = ∑ s, Pi.single s (x s) := (Finset.univ_sum_single x).symm
    rw [hx]
    refine Finset.sum_induction _ (fun x => heisB H v * heisXaProd H (Multiplicative.ofAdd x) *
        (heisB H v)⁻¹ = heisXaProd H (Multiplicative.ofAdd x) * H.z (heisBeta H x v)) ?_ ?_ ?_
    · intro x y hx hy
      have hzc : ∀ c : K, H.z c * heisXaProd H (Multiplicative.ofAdd y) =
          heisXaProd H (Multiplicative.ofAdd y) * H.z c := fun c =>
        heisZ_comm_xaProd H (Multiplicative.ofAdd c) _
      calc heisB H v * heisXaProd H (Multiplicative.ofAdd (x + y)) * (heisB H v)⁻¹
          = (heisB H v * heisXaProd H (Multiplicative.ofAdd x) * (heisB H v)⁻¹) *
            (heisB H v * heisXaProd H (Multiplicative.ofAdd y) * (heisB H v)⁻¹) := by
            rw [ofAdd_add, map_mul]; group
        _ = heisXaProd H (Multiplicative.ofAdd x) * H.z (heisBeta H x v) *
            (heisXaProd H (Multiplicative.ofAdd y) * H.z (heisBeta H y v)) := by rw [hx, hy]
        _ = heisXaProd H (Multiplicative.ofAdd x) *
            (H.z (heisBeta H x v) * heisXaProd H (Multiplicative.ofAdd y)) *
            H.z (heisBeta H y v) := by simp only [mul_assoc]
        _ = heisXaProd H (Multiplicative.ofAdd x) *
            (heisXaProd H (Multiplicative.ofAdd y) * H.z (heisBeta H x v)) *
            H.z (heisBeta H y v) := by rw [hzc]
        _ = heisXaProd H (Multiplicative.ofAdd (x + y)) * H.z (heisBeta H (x + y) v) := by
            rw [ofAdd_add, map_mul, map_add, LinearMap.add_apply, H.z_add]
            simp only [mul_assoc]
    · simp [H.z_zero]
    · intro s _
      rw [heisXaProd_single]
      have h1 := H.comm_yElt_xa v s (x s)
      rw [commutatorElement_def, inv_inv] at h1
      have h2 : heisB H v * H.xa s (x s) * (heisB H v)⁻¹ = H.z (H.ε s * v s * x s) * H.xa s (x s) := by
        rw [heisB, inv_inv]
        calc (H.yElt v)⁻¹ * H.xa s (x s) * H.yElt v
            = ((H.yElt v)⁻¹ * H.xa s (x s) * H.yElt v * (H.xa s (x s))⁻¹) * H.xa s (x s) := by
              group
          _ = _ := by rw [h1]
      rw [h2]
      have h3 : heisBeta H (Pi.single s (x s)) v = H.ε s * v s * x s := by
        rw [heisBeta_apply, Finset.sum_eq_single s]
        · simp only [Pi.single_eq_same]; ring
        · intro j _ hj; simp [hj]
        · intro h; exact absurd (Finset.mem_univ s) h
      rw [h3]
      exact H.z_comm_a _ s _
  exact key u

end Generic

section Engine

theorem two_pow_le_card_of_heisSystem {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w * w = 1) {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {L : Subgroup (MulAut W)} {Sg : Type} [Group Sg] (π : ↥L →* Sg)
    (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center ↥L)
    (hZ : ¬ p ∣ Nat.card π.ker)
    {K : Type} [Field K] [Finite K] [CharP K p] {S : Type} [Fintype S] [DecidableEq S]
    {Γ : Type} [Group Γ] (H : HeisSystem Γ K S) (f : Γ →* Sg) (hf : f.ker ≤ Subgroup.center Γ)
    (hnc : ∀ c : K, H.z c ∈ Subgroup.center Γ → c = 0)
    {T : Type} [Group T] (t : T →* Sg) (χ : T →* Kˣ)
    (htz : ∀ s c, t s * f (H.z c) * (t s)⁻¹ = f (H.z ((χ s : K) * c)))
    (hta : ∀ s u, ∃ u', t s * f (heisXaProd H (Multiplicative.ofAdd u)) * (t s)⁻¹ =
      f (heisXaProd H (Multiplicative.ofAdd u'))) :
    2 ^ (orderOf (2 : ZMod p) * (Nat.card χ.range * Nat.card (S → K) / (p - 1))) ≤
      Nat.card W := by
  classical
  refine two_pow_le_card_of_heis_root hW hp2 π hπ hker hZ (K := K) (V := S → K)
    (f.comp (heisZ H)) (f.comp (heisXaProd H)) (fun v => f (heisB H v)) (heisBeta H)
    (fun v hv => heisBeta_nondeg_right H hv) ?_ ?_ ?_ ?_ t χ ?_ ?_
  · intro c u h
    have h1 : f (H.z c * heisXaProd H (Multiplicative.ofAdd u)) = 1 := by
      rw [map_mul]; exact h
    have hgc := Subgroup.mem_center_iff.1 (hf (MonoidHom.mem_ker.2 h1))
    have hβ0 : ∀ v : S → K, heisBeta H u v = 0 := by
      intro v
      have e1 : heisB H v * (H.z c * heisXaProd H (Multiplicative.ofAdd u)) * (heisB H v)⁻¹ =
          H.z c * heisXaProd H (Multiplicative.ofAdd u) * H.z (heisBeta H u v) := by
        have hb : heisB H v * H.z c = H.z c * heisB H v := heisB_comm_z H (Multiplicative.ofAdd c) v
        calc heisB H v * (H.z c * heisXaProd H (Multiplicative.ofAdd u)) * (heisB H v)⁻¹
            = (heisB H v * H.z c) * heisXaProd H (Multiplicative.ofAdd u) * (heisB H v)⁻¹ := by
              simp only [mul_assoc]
          _ = H.z c * (heisB H v * heisXaProd H (Multiplicative.ofAdd u) * (heisB H v)⁻¹) := by
              rw [hb]; simp only [mul_assoc]
          _ = _ := by rw [heisXaProd_conj, mul_assoc]
      have e2 : heisB H v * (H.z c * heisXaProd H (Multiplicative.ofAdd u)) * (heisB H v)⁻¹ =
          H.z c * heisXaProd H (Multiplicative.ofAdd u) := by
        rw [hgc (heisB H v)]; group
      rw [e2] at e1
      have e3 : H.z (heisBeta H u v) = 1 := (mul_eq_left.1 e1.symm)
      exact H.z_injective (e3.trans H.z_zero.symm)
    have hu : u = 0 := by
      by_contra hu0
      obtain ⟨v, hv⟩ := heisBeta_nondeg_left H hu0
      exact hv (hβ0 v)
    subst hu
    refine ⟨hnc c ?_, rfl⟩
    have h2 : H.z c * heisXaProd H (Multiplicative.ofAdd (0 : S → K)) = H.z c := by
      rw [ofAdd_zero, map_one, mul_one]
    rw [h2] at hgc
    exact Subgroup.mem_center_iff.2 hgc
  · intro c u
    show f (heisZ H c) * f (heisXaProd H u) = f (heisXaProd H u) * f (heisZ H c)
    rw [← map_mul, ← map_mul, heisZ_comm_xaProd]
  · intro u v
    show f (heisB H v) * f (heisXaProd H (Multiplicative.ofAdd u)) * (f (heisB H v))⁻¹ =
      f (heisXaProd H (Multiplicative.ofAdd u)) * f (H.z (heisBeta H u v))
    rw [← map_inv, ← map_mul, ← map_mul, ← map_mul, heisXaProd_conj]
  · intro c v
    show f (heisB H v) * f (heisZ H c) = f (heisZ H c) * f (heisB H v)
    rw [← map_mul, ← map_mul, heisB_comm_z]
  · exact htz
  · exact hta

end Engine

end CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit
