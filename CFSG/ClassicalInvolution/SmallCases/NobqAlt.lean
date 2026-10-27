module

public import CFSG.ClassicalInvolution.SmallCases.NobqOut
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.BenderGroupFactsAlternating
public import Certificates.Certificate9301

public section

namespace CFSG.ClassicalInvolution.Nobq

namespace AltWitness

open Equiv Equiv.Perm

variable {α : Type*} {γ τ : Perm α}

theorem tau_apply (hγ : γ * γ = τ) (x : α) : τ x = γ (γ x) := by rw [← hγ]; rfl

theorem gamma_four (hγ : γ * γ = τ) (hτ : τ * τ = 1) (x : α) : γ (γ (γ (γ x))) = x := by
  have h : (γ * γ) * (γ * γ) = 1 := by rw [hγ, hτ]
  have := congrArg (fun f : Perm α => f x) h
  simpa using this

theorem orbit_ne (hγ : γ * γ = τ) (hτ : τ * τ = 1) {x : α} (hx : τ x ≠ x) :
    γ x ≠ x ∧ γ (γ x) ≠ x ∧ γ (γ (γ x)) ≠ x ∧ γ x ≠ γ (γ x) ∧ γ x ≠ γ (γ (γ x)) ∧
      γ (γ x) ≠ γ (γ (γ x)) := by
  have h4 := gamma_four hγ hτ x
  have h1 : γ x ≠ x := fun h => hx (by rw [tau_apply hγ, h, h])
  have h2 : γ (γ x) ≠ x := fun h => hx (by rw [tau_apply hγ]; exact h)
  have h3 : γ (γ (γ x)) ≠ x := fun h => h1 (by
    have := congrArg γ h
    rw [h4] at this
    exact this.symm)
  refine ⟨h1, h2, h3, fun h => h1 (γ.injective h).symm, fun h => h2 (γ.injective h).symm,
    fun h => h1 (γ.injective (γ.injective h)).symm⟩


theorem cross_ne {p p' : α} (hc : ¬ γ.SameCycle p p') :
    p ≠ p' ∧ p ≠ γ p' ∧ p ≠ γ (γ p') ∧ p ≠ γ (γ (γ p')) ∧
    γ p ≠ p' ∧ γ p ≠ γ p' ∧ γ p ≠ γ (γ p') ∧ γ p ≠ γ (γ (γ p')) ∧
    γ (γ p) ≠ p' ∧ γ (γ p) ≠ γ p' ∧ γ (γ p) ≠ γ (γ p') ∧ γ (γ p) ≠ γ (γ (γ p')) ∧
    γ (γ (γ p)) ≠ p' ∧ γ (γ (γ p)) ≠ γ p' ∧ γ (γ (γ p)) ≠ γ (γ p') ∧
      γ (γ (γ p)) ≠ γ (γ (γ p')) := by
  have key : ∀ a b : α, γ.SameCycle p a → γ.SameCycle p' b → a ≠ b :=
    fun a b ha hb hab => hc (ha.trans (hab ▸ hb.symm))
  have s0 : γ.SameCycle p p := Equiv.Perm.SameCycle.refl γ p
  have s1 : γ.SameCycle p (γ p) := by simpa [Equiv.Perm.sameCycle_apply_right] using s0
  have s2 : γ.SameCycle p (γ (γ p)) := by simpa [Equiv.Perm.sameCycle_apply_right] using s0
  have s3 : γ.SameCycle p (γ (γ (γ p))) := by simpa [Equiv.Perm.sameCycle_apply_right] using s0
  have t0 : γ.SameCycle p' p' := Equiv.Perm.SameCycle.refl γ p'
  have t1 : γ.SameCycle p' (γ p') := by simpa [Equiv.Perm.sameCycle_apply_right] using t0
  have t2 : γ.SameCycle p' (γ (γ p')) := by simpa [Equiv.Perm.sameCycle_apply_right] using t0
  have t3 : γ.SameCycle p' (γ (γ (γ p'))) := by simpa [Equiv.Perm.sameCycle_apply_right] using t0
  exact ⟨key _ _ s0 t0, key _ _ s0 t1, key _ _ s0 t2, key _ _ s0 t3,
    key _ _ s1 t0, key _ _ s1 t1, key _ _ s1 t2, key _ _ s1 t3,
    key _ _ s2 t0, key _ _ s2 t1, key _ _ s2 t2, key _ _ s2 t3,
    key _ _ s3 t0, key _ _ s3 t1, key _ _ s3 t2, key _ _ s3 t3⟩


theorem caseI_inj (hγ : γ * γ = τ) (hτ : τ * τ = 1) {p p' : α} (hp : τ p ≠ p)
    (hp' : τ p' ≠ p') (hc : ¬ γ.SameCycle p p') :
    Function.Injective (![p, γ p, γ (γ p), γ (γ (γ p)), p', γ p', γ (γ p'),
      γ (γ (γ p'))] : Fin 8 → α) := by
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := orbit_ne hγ hτ hp
  obtain ⟨b1, b2, b3, b4, b5, b6⟩ := orbit_ne hγ hτ hp'
  obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15⟩ := cross_ne hc
  intro i j h
  fin_cases i <;> fin_cases j <;> first | rfl | (exfalso; simp at h; first
    | exact absurd h ‹_› | exact absurd h.symm ‹_›)


def sigma8 : Perm (Fin 8) :=
  ⟨![1, 2, 3, 0, 5, 6, 7, 4], ![3, 0, 1, 2, 7, 4, 5, 6], by decide, by decide⟩

def g8 : Perm (Fin 8) := swap 0 4 * swap 2 6

variable [DecidableEq α]

theorem exists_witness_of_ne_sameCycle [Fintype α] (hγ : γ * γ = τ) (hτ : τ * τ = 1)
    {p p' : α} (hp : τ p ≠ p)
    (hp' : τ p' ≠ p') (hc : ¬ γ.SameCycle p p') :
    ∃ g : Perm α, sign g = 1 ∧ g * τ = τ * g ∧
      (γ * (g * γ * g⁻¹)) * (γ * (g * γ * g⁻¹)) = 1 ∧ γ * (g * γ * g⁻¹) ≠ 1 ∧
        γ * (g * γ * g⁻¹) ≠ τ := by
  have hinj := caseI_inj hγ hτ hp hp' hc
  have h4 := gamma_four hγ hτ
  set φ : Fin 8 → α := ![p, γ p, γ (γ p), γ (γ (γ p)), p', γ p', γ (γ p'),
    γ (γ (γ p'))] with hφ
  have hγφ : ∀ i, γ (φ i) = φ (sigma8 i) := by
    intro i
    fin_cases i <;> simp [φ, sigma8, h4 p, h4 p']
  have hτφ : ∀ i, τ (φ i) = φ (sigma8 (sigma8 i)) := by
    intro i
    rw [tau_apply hγ, hγφ, hγφ]
  set g : Perm α := swap p p' * swap (γ (γ p)) (γ (γ p')) with hg
  have hgφ : ∀ i, g (φ i) = φ (g8 i) := by
    intro i
    have e1 : g (φ i) = swap (φ 0) (φ 4) (swap (φ 2) (φ 6) (φ i)) := rfl
    rw [e1, hinj.swap_apply, hinj.swap_apply]
    rfl
  have hgz : ∀ z, (∀ i, z ≠ φ i) → g z = z := by
    intro z hz
    have h1 : z ≠ p := hz 0
    have h2 : z ≠ p' := hz 4
    have h3 : z ≠ γ (γ p) := hz 2
    have h5 : z ≠ γ (γ p') := hz 6
    show swap p p' (swap (γ (γ p)) (γ (γ p')) z) = z
    rw [swap_apply_of_ne_of_ne h3 h5, swap_apply_of_ne_of_ne h1 h2]
  have hγz : ∀ z, (∀ i, z ≠ φ i) → ∀ i, γ z ≠ φ i := by
    intro z hz i hzi
    apply hz (sigma8 (sigma8 (sigma8 i)))
    have : z = γ (γ (γ (γ z))) := (h4 z).symm
    rw [this, hzi, hγφ, hγφ, hγφ]
  have hg8 : ∀ i, g8 (g8 i) = i := by decide
  have hgg : g * g = 1 := by
    ext z
    by_cases hz : ∀ i, z ≠ φ i
    · simp [Perm.mul_apply, hgz z hz]
    · push Not at hz
      obtain ⟨i, rfl⟩ := hz
      simp [Perm.mul_apply, hgφ, hg8]
  have hginv : g⁻¹ = g := inv_eq_of_mul_eq_one_right hgg
  have hhφ : ∀ i, (γ * g) (φ i) = φ ((sigma8 * g8) i) := by
    intro i
    rw [Perm.mul_apply, hgφ, hγφ]
    rfl
  have hhz : ∀ z, (∀ i, z ≠ φ i) → (γ * g) z = γ z := by
    intro z hz
    rw [Perm.mul_apply, hgz z hz]
  have hh4 : ∀ z, (γ * g) ((γ * g) ((γ * g) ((γ * g) z))) = z := by
    intro z
    by_cases hz : ∀ i, z ≠ φ i
    · have e1 := hhz z hz
      have e2 := hhz (γ z) (hγz z hz)
      have e3 := hhz (γ (γ z)) (hγz _ (hγz z hz))
      have e4 := hhz (γ (γ (γ z))) (hγz _ (hγz _ (hγz z hz)))
      calc (γ * g) ((γ * g) ((γ * g) ((γ * g) z))) = (γ * g) ((γ * g) ((γ * g) (γ z))) := by
            rw [e1]
        _ = (γ * g) ((γ * g) (γ (γ z))) := by rw [e2]
        _ = (γ * g) (γ (γ (γ z))) := by rw [e3]
        _ = γ (γ (γ (γ z))) := by rw [e4]
        _ = z := h4 z
    · push Not at hz
      obtain ⟨i, rfl⟩ := hz
      have hk : ∀ i, (sigma8 * g8) ((sigma8 * g8) ((sigma8 * g8) ((sigma8 * g8) i))) = i := by
        decide
      rw [hhφ, hhφ, hhφ, hhφ, hk]
  have hxx : γ * (g * γ * g⁻¹) = (γ * g) * (γ * g) := by
    rw [hginv]
    simp only [mul_assoc]
  obtain ⟨c0, -, -, -, -, -, -, -, -, -, c10, -⟩ := cross_ne hc
  have hpp' : p ≠ p' := c0
  have hpp'' : γ (γ p) ≠ γ (γ p') := c10
  refine ⟨g, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hg, Perm.sign_mul, sign_swap hpp', sign_swap hpp'']
    norm_num
  · ext z
    show g (τ z) = τ (g z)
    by_cases hz : ∀ i, z ≠ φ i
    · have hτz : τ z = γ (γ z) := tau_apply hγ z
      have hτz' : ∀ i, τ z ≠ φ i := by
        rw [hτz]
        exact hγz _ (hγz z hz)
      rw [hgz z hz, hgz _ hτz']
    · push Not at hz
      obtain ⟨i, rfl⟩ := hz
      have hc8 : ∀ i, g8 (sigma8 (sigma8 i)) = sigma8 (sigma8 (g8 i)) := by decide
      rw [hτφ, hgφ, hgφ, hτφ, hc8]
  · rw [hxx]
    ext z
    simp only [Perm.mul_apply, Perm.one_apply]
    exact hh4 z
  · rw [hxx]
    intro h1
    have h2 := congrArg (fun f : Perm α => f (φ 0)) h1
    change (γ * g) ((γ * g) (φ 0)) = φ 0 at h2
    rw [hhφ, hhφ] at h2
    have h3 := hinj h2
    revert h3
    decide
  · rw [hxx]
    intro h1
    have h2 := congrArg (fun f : Perm α => f (φ 0)) h1
    change (γ * g) ((γ * g) (φ 0)) = τ (φ 0) at h2
    rw [hhφ, hhφ, hτφ] at h2
    have h3 := hinj h2
    revert h3
    decide


theorem sign_of_fixedPointFree (d : Perm (Fin 4)) (h : ∀ i, (d * d) i ≠ i) : sign d = -1 := by
  revert d
  decide +revert

theorem exists_commuting_odd (d : Perm (Fin 4))
    (h : ∀ i, (d * d) i ≠ i) (ε : ℤˣ) :
    ∃ u : Perm (Fin 4), sign u = ε ∧ u * (d * d) = (d * d) * u ∧
      (d * (u * d * u⁻¹)) * (d * (u * d * u⁻¹)) = 1 := by
  revert d ε
  exact Certificates.certificate9301.1

theorem exists_conj_involution (m : ℕ)
    (hm : m = 4 ∨ m = 5 ∨ m = 6 ∨ m = 7) (r : Perm (Fin m)) (hr : r * r = 1) (hr1 : r ≠ 1) :
    ∃ v : Perm (Fin m), (r * (v * r * v⁻¹)) * (r * (v * r * v⁻¹)) = 1 ∧ r * (v * r * v⁻¹) ≠ 1 := by
  rcases hm with rfl | rfl | rfl | rfl
  · revert r; exact Certificates.certificate9301.2.1
  · revert r; exact Certificates.certificate9301.2.2.1
  · revert r; exact Certificates.certificate9301.2.2.2.1
  · revert r; exact Certificates.certificate9301.2.2.2.2


omit [DecidableEq α] in
theorem moved_mem_orbit (hγ : γ * γ = τ) (hτ : τ * τ = 1) {p : α}
    (hII : ∀ x, τ x ≠ x → γ.SameCycle p x) {x : α} (hx : τ x ≠ x) :
    x = p ∨ x = γ p ∨ x = γ (γ p) ∨ x = γ (γ (γ p)) := by
  obtain ⟨k, hk⟩ := hII x hx
  have h4 : γ ^ (4 : ℤ) = 1 := by
    have : γ ^ 4 = 1 := by
      have h : (γ * γ) * (γ * γ) = 1 := by rw [hγ, hτ]
      calc γ ^ 4 = γ ^ 2 * γ ^ 2 := by rw [← pow_add]
        _ = (γ * γ) * (γ * γ) := by rw [pow_two]
        _ = 1 := h
    exact_mod_cast this
  rw [zpow_eq_zpow_emod k h4] at hk
  have h0 : 0 ≤ k % 4 := Int.emod_nonneg k (by norm_num)
  have h1 : k % 4 < 4 := Int.emod_lt_of_pos k (by norm_num)
  generalize k % 4 = r at hk h0 h1
  interval_cases r
  · left; simpa using hk.symm
  · right; left; simpa using hk.symm
  · right; right; left; simpa [zpow_ofNat, pow_two, Perm.mul_apply] using hk.symm
  · right; right; right
    have : (γ ^ (3 : ℤ)) p = γ (γ (γ p)) := by
      rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) by norm_num, zpow_natCast, pow_succ, pow_two]
      simp [Perm.mul_apply]
    rw [← this]; exact hk.symm


theorem exists_witness_of_single_cycle
    [Fintype α] (hγ : γ * γ = τ) (hτ : τ * τ = 1)
    (hs : sign γ = 1)
    {p : α} (hp : τ p ≠ p) (hII : ∀ x, τ x ≠ x → γ.SameCycle p x)
    {m : ℕ} (hm : m = 4 ∨ m = 5 ∨ m = 6 ∨ m = 7) (hcard : Fintype.card α = m + 4) :
    ∃ g : Perm α, sign g = 1 ∧ g * τ = τ * g ∧
      (γ * (g * γ * g⁻¹)) * (γ * (g * γ * g⁻¹)) = 1 ∧ γ * (g * γ * g⁻¹) ≠ 1 ∧
        γ * (g * γ * g⁻¹) ≠ τ := by
  have hcomm : γ * τ = τ * γ := by
    rw [← hγ]
    exact (mul_assoc γ γ γ).symm
  have hcomm' : ∀ x, γ (τ x) = τ (γ x) := fun x => congrArg (fun f : Perm α => f x) hcomm
  have hpres : ∀ x, τ x = x ↔ τ (γ x) = γ x := by
    intro x
    rw [← hcomm' x]
    exact (γ.injective.eq_iff).symm
  have hmoved : ∀ x, τ x ≠ x → τ (γ x) ≠ γ x := fun x hx h => hx ((hpres x).2 h)
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := orbit_ne hγ hτ hp
  let φ4 : Fin 4 → α := ![p, γ p, γ (γ p), γ (γ (γ p))]
  have hφ4 : ∀ i, ¬ τ (φ4 i) = φ4 i := by
    intro i
    fin_cases i
    · exact hp
    · exact hmoved _ hp
    · exact hmoved _ (hmoved _ hp)
    · exact hmoved _ (hmoved _ (hmoved _ hp))
  have hinj4 : Function.Injective φ4 := by
    intro i j h
    fin_cases i <;> fin_cases j <;>
      first | rfl | (exfalso; simp [φ4] at h; first | exact absurd h ‹_› | exact absurd h.symm ‹_›)
  let f : Fin 4 → {x // ¬ τ x = x} := fun i => ⟨φ4 i, hφ4 i⟩
  have hf : Function.Bijective f := by
    refine ⟨fun i j h => hinj4 (congrArg Subtype.val h), fun ⟨x, hx⟩ => ?_⟩
    rcases moved_mem_orbit hγ hτ hII hx with h | h | h | h
    · exact ⟨0, Subtype.ext h.symm⟩
    · exact ⟨1, Subtype.ext h.symm⟩
    · exact ⟨2, Subtype.ext h.symm⟩
    · exact ⟨3, Subtype.ext h.symm⟩
  let eM : Fin 4 ≃ {x // ¬ τ x = x} := Equiv.ofBijective f hf
  have hcardM : Fintype.card {x // ¬ τ x = x} = 4 := by
    rw [← Fintype.card_fin 4]
    exact (Fintype.card_congr eM).symm
  have hcardF : Fintype.card {x // τ x = x} = m := by
    have := Fintype.card_subtype_compl (fun x => τ x = x)
    omega
  let eF : Fin m ≃ {x // τ x = x} := (Fintype.equivFinOfCardEq hcardF).symm
  let Φ : Perm (Fin m) × Perm (Fin 4) →* Perm α :=
    (subtypeCongrHom (fun x : α => τ x = x)).comp
      (MulEquiv.prodCongr eF.permCongrHom eM.permCongrHom).toMonoidHom
  have hΦinj : Function.Injective Φ :=
    (subtypeCongrHom_injective _).comp
      (MulEquiv.prodCongr eF.permCongrHom eM.permCongrHom).injective
  have hΦ : ∀ (a : Perm (Fin m)) (b : Perm (Fin 4)),
      Φ (a, b) = (eF.permCongr a).subtypeCongr (eM.permCongr b) := fun a b => rfl
  have hsignΦ : ∀ (a : Perm (Fin m)) (b : Perm (Fin 4)), sign (Φ (a, b)) = sign a * sign b := by
    intro a b
    rw [hΦ, sign_subtypeCongr, sign_permCongr, sign_permCongr]
  let r : Perm {x // τ x = x} := γ.subtypePerm (fun x => (hpres x).symm)
  let d : Perm {x // ¬ τ x = x} := γ.subtypePerm (fun x => not_congr (hpres x).symm)
  have hγr : r.subtypeCongr d = γ := by
    ext x
    by_cases hx : τ x = x
    · rw [Perm.subtypeCongr.left_apply r d hx]
      rfl
    · rw [Perm.subtypeCongr.right_apply r d hx]
      rfl
  let a : Perm (Fin m) := eF.permCongrHom.symm r
  let b : Perm (Fin 4) := eM.permCongrHom.symm d
  have hΦγ : Φ (a, b) = γ := by
    rw [hΦ, ← hγr]
    have h1 : eF.permCongr a = r := eF.permCongrHom.apply_symm_apply r
    have h2 : eM.permCongr b = d := eM.permCongrHom.apply_symm_apply d
    rw [h1, h2]
  have hΦτ : Φ (a * a, b * b) = τ := by
    have : (a * a, b * b) = (a, b) * (a, b) := rfl
    rw [this, map_mul, hΦγ, hγ]
  have hrr : r * r = 1 := by
    ext x
    show γ (γ x) = x
    rw [← tau_apply hγ]
    exact x.2
  have haa : a * a = 1 := by
    have : eF.permCongrHom (a * a) = 1 := by
      rw [map_mul]
      simp only [a, MulEquiv.apply_symm_apply]
      exact hrr
    exact eF.permCongrHom.injective (this.trans (map_one _).symm)
  have hdd : ∀ y : {x // ¬ τ x = x}, (d * d) y ≠ y := by
    intro y h
    apply y.2
    have : ((d * d) y : α) = γ (γ y) := rfl
    rw [h] at this
    rw [tau_apply hγ]
    exact this.symm
  have hbb : ∀ i, (b * b) i ≠ i := by
    intro i h
    apply hdd (eM i)
    have : eM.permCongrHom (b * b) = d * d := by
      rw [map_mul]
      simp only [b, MulEquiv.apply_symm_apply]
    rw [← this]
    show eM ((b * b) (eM.symm (eM i))) = eM i
    rw [Equiv.symm_apply_apply, h]
  have hsb : sign b = -1 := sign_of_fixedPointFree b hbb
  have hsa : sign a = -1 := by
    have h1 : sign a * sign b = 1 := by rw [← hsignΦ, hΦγ]; exact hs
    rw [hsb] at h1
    rcases Int.units_eq_one_or (sign a) with h | h
    · rw [h] at h1
      exact absurd h1 (by decide)
    · exact h
  have ha1 : a ≠ 1 := fun h => by
    rw [h, map_one] at hsa
    exact absurd hsa (by decide)
  obtain ⟨v, hv1, hv2⟩ := exists_conj_involution m hm a haa ha1
  obtain ⟨u, hus, hucomm, hu2⟩ := exists_commuting_odd b hbb (sign v)
  have hx : γ * (Φ (v, u) * γ * (Φ (v, u))⁻¹) =
      Φ (a * (v * a * v⁻¹), b * (u * b * u⁻¹)) := by
    rw [← hΦγ]
    simp only [← map_inv, ← map_mul, Prod.mk_mul_mk, Prod.inv_mk]
  refine ⟨Φ (v, u), ?_, ?_, ?_, ?_, ?_⟩
  · rw [hsignΦ, hus]
    exact Int.units_mul_self _
  · have e : (v, u) * (a * a, b * b) = (a * a, b * b) * (v, u) := by
      refine Prod.ext ?_ ?_
      · show v * (a * a) = (a * a) * v
        rw [haa, mul_one, one_mul]
      · exact hucomm
    calc Φ (v, u) * τ = Φ ((v, u) * (a * a, b * b)) := by rw [map_mul, hΦτ]
      _ = Φ ((a * a, b * b) * (v, u)) := by rw [e]
      _ = τ * Φ (v, u) := by rw [map_mul, hΦτ]
  · rw [hx, ← map_mul, Prod.mk_mul_mk, hv1, hu2]
    have h11 : ((1 : Perm (Fin m)), (1 : Perm (Fin 4))) = 1 := rfl
    rw [h11, map_one]
  · rw [hx]
    intro h
    have := hΦinj (h.trans (map_one Φ).symm)
    exact hv2 (congrArg Prod.fst this)
  · rw [hx, ← hΦτ]
    intro h
    have := hΦinj h
    have h1 := congrArg Prod.fst this
    simp only at h1
    apply hv2
    rw [h1, haa]


theorem exists_witness
    [Fintype α] (hγ : γ * γ = τ) (hτ : τ * τ = 1) (hτ1 : τ ≠ 1)
    (hs : sign γ = 1) (hcard : 8 ≤ Fintype.card α) (hcard' : Fintype.card α ≤ 11) :
    ∃ g : Perm α, sign g = 1 ∧ g * τ = τ * g ∧
      (γ * (g * γ * g⁻¹)) * (γ * (g * γ * g⁻¹)) = 1 ∧ γ * (g * γ * g⁻¹) ≠ 1 ∧
        γ * (g * γ * g⁻¹) ≠ τ := by
  obtain ⟨p, hp⟩ : ∃ p, τ p ≠ p := by
    by_contra h
    push Not at h
    exact hτ1 (Equiv.ext h)
  by_cases hc : ∃ p', τ p' ≠ p' ∧ ¬ γ.SameCycle p p'
  · obtain ⟨p', hp', hcp⟩ := hc
    exact exists_witness_of_ne_sameCycle hγ hτ hp hp' hcp
  · push Not at hc
    exact exists_witness_of_single_cycle hγ hτ hs hp hc (m := Fintype.card α - 4) (by omega)
      (by omega)

end AltWitness

open AltWitness in
theorem noUniqueInvNormal_alternating
    (n : ℕ) (h8 : 8 ≤ n) (h11 : n ≤ 11) :
    NoUniqueInvNormal (alternatingGroup (Fin n)) := by
  intro t N ht
  refine not_uniqueInvNormal_of_witness fun c hc hct => ?_
  have hγ : (c : Equiv.Perm (Fin n)) * c = t := congrArg Subtype.val hct
  have hτ : (t : Equiv.Perm (Fin n)) * t = 1 := by
    have : t * t = 1 := by
      have := pow_orderOf_eq_one t
      rwa [ht, pow_two] at this
    exact congrArg Subtype.val this
  have hτ1 : (t : Equiv.Perm (Fin n)) ≠ 1 := by
    intro h
    have : t = 1 := Subtype.ext h
    rw [this, orderOf_one] at ht
    exact absurd ht (by norm_num)
  obtain ⟨g, hgs, hgτ, h1, h2, h3⟩ := exists_witness hγ hτ hτ1
    (Equiv.Perm.mem_alternatingGroup.1 c.2) (by simpa using h8) (by simpa using h11)
  refine ⟨⟨g, Equiv.Perm.mem_alternatingGroup.2 hgs⟩, ?_, ?_, ?_, ?_⟩
  · rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subtype.ext hgτ
  · apply Subtype.ext
    simpa using h1
  · intro h
    exact h2 (by simpa using congrArg Subtype.val h)
  · intro h
    exact h3 (by simpa using congrArg Subtype.val h)

theorem noDatum_alternating (n : ℕ) (h8 : 8 ≤ n) (h11 : n ≤ 11) :
    NoDatum (alternatingGroup (Fin n)) :=
  noDatum_of_noUniqueInvNormal (noUniqueInvNormal_alternating n h8 h11)
    (OutTwoCyclic.of_card_le_two
      (CFSG.ProperTwoGeneratedCore.BenderFacts.card_outer_alternatingGroup (by omega)
        (by omega)).le)

end CFSG.ClassicalInvolution.Nobq
