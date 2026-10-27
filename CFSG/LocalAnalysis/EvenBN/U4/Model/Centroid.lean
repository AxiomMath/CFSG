module

public import CFSG.LocalAnalysis.EvenBN.U4.Model.Basic

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.U4

open Matrix Subgroup CFSG.LocalAnalysis CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)

section Pairing

@[expose] def miyamotoPairing (v w : K × K) : K :=
  h.bar v.1 * w.2 + v.1 * h.bar w.2 + h.bar w.1 * v.2 + w.1 * h.bar v.2

theorem miyamotoPairing_apply (a c a' c' : K) :
    miyamotoPairing h (a, c) (a', c') =
      h.bar a * c' + a * h.bar c' + h.bar a' * c + a' * h.bar c :=
  rfl

theorem miyamotoXGL_commutator_A2_eq_pairing [CharP K 2] (a c d a' c' d' : K) :
    ⁅miyamotoXGL h a 0 c d, miyamotoXGL h a' 0 c' d'⁆ =
      miyamotoXGL h 0 0 0 (miyamotoPairing h (a, c) (a', c')) :=
  miyamotoXGL_commutator_A2 h a c d a' c' d'

theorem bar_miyamotoPairing (v w : K × K) :
    h.bar (miyamotoPairing h v w) = miyamotoPairing h v w := by
  simp only [miyamotoPairing, map_add, map_mul, h.bar_bar]
  ring

theorem miyamotoPairing_comm (v w : K × K) : miyamotoPairing h v w = miyamotoPairing h w v := by
  simp only [miyamotoPairing]
  ring

theorem miyamotoPairing_add_left (v v' w : K × K) :
    miyamotoPairing h (v + v') w = miyamotoPairing h v w + miyamotoPairing h v' w := by
  simp only [miyamotoPairing, Prod.fst_add, Prod.snd_add, map_add]
  ring

theorem miyamotoPairing_add_right (v w w' : K × K) :
    miyamotoPairing h v (w + w') = miyamotoPairing h v w + miyamotoPairing h v w' := by
  rw [miyamotoPairing_comm, miyamotoPairing_add_left, miyamotoPairing_comm h w,
    miyamotoPairing_comm h w']

@[simp] theorem miyamotoPairing_zero_left (w : K × K) : miyamotoPairing h 0 w = 0 := by
  simp [miyamotoPairing]

@[simp] theorem miyamotoPairing_zero_right (v : K × K) : miyamotoPairing h v 0 = 0 := by
  simp [miyamotoPairing]

theorem miyamotoPairing_smul_left {t : K} (ht : h.bar t = t) (v w : K × K) :
    miyamotoPairing h (t • v) w = t * miyamotoPairing h v w := by
  simp only [miyamotoPairing, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, map_mul, ht]
  ring

theorem miyamotoPairing_smul_right {t : K} (ht : h.bar t = t) (v w : K × K) :
    miyamotoPairing h v (t • w) = t * miyamotoPairing h v w := by
  rw [miyamotoPairing_comm, miyamotoPairing_smul_left h ht, miyamotoPairing_comm]

theorem miyamotoPairing_sub_left (v v' w : K × K) :
    miyamotoPairing h (v - v') w = miyamotoPairing h v w - miyamotoPairing h v' w := by
  simp only [miyamotoPairing, Prod.fst_sub, Prod.snd_sub, map_sub]
  ring

theorem miyamotoPairing_self [CharP K 2] (v : K × K) : miyamotoPairing h v v = 0 := by
  simp only [miyamotoPairing]
  linear_combination (h.bar v.1 * v.2 + v.1 * h.bar v.2) * CharTwo.two_eq_zero (R := K)

theorem eq_zero_of_miyamotoPairing [CharP K 2] {v : K × K}
    (hv : ∀ w, miyamotoPairing h v w = 0) : v = 0 := by
  obtain ⟨ω, hω⟩ := h.exists_bar_ne
  obtain ⟨a, c⟩ := v
  have e1 := hv (0, 1)
  have e2 := hv (0, ω)
  have e3 := hv (1, 0)
  have e4 := hv (ω, 0)
  simp only [miyamotoPairing_apply, map_one, map_zero, mul_one, one_mul, mul_zero, zero_mul,
    add_zero, zero_add] at e1 e2 e3 e4
  have ha : a = 0 := eq_zero_of_trace_mul h hω (by linear_combination e1)
    (by linear_combination e2)
  have hc : c = 0 := eq_zero_of_trace_mul h hω (by linear_combination e3)
    (by linear_combination e4)
  rw [ha, hc]
  rfl

theorem exists_miyamotoPairing_eq {s : K} (hs : h.bar s = s) :
    ∃ c' : K, miyamotoPairing h (1, 0) (0, c') = s := by
  obtain ⟨c', hc'⟩ := h.traceLin_surjective ⟨s, hs⟩
  refine ⟨c', ?_⟩
  have : c' + h.bar c' = s := congrArg Subtype.val hc'
  simpa [miyamotoPairing_apply] using this

end Pairing

section Centroid

variable [CharP K 2]

theorem miyamotoPairing_centroid (θ : K × K →+ K × K) (χ : K → K)
    (hχ : ∀ v w, χ (miyamotoPairing h v w) = miyamotoPairing h (θ v) w) :
    ∃ μ : K, h.bar μ = μ ∧ (∀ v, θ v = μ • v) ∧ ∀ s, h.bar s = s → χ s = μ * s := by
  have hlin : ∀ t s : K, h.bar t = t → h.bar s = s → χ (t * s) = t * χ s := by
    intro t s ht hs
    obtain ⟨c', rfl⟩ := exists_miyamotoPairing_eq h hs
    rw [← miyamotoPairing_smul_right h ht, hχ, hχ, miyamotoPairing_smul_right h ht]
  obtain ⟨c₁, hc₁⟩ := exists_miyamotoPairing_eq h (map_one h.bar)
  refine ⟨χ 1, ?_, ?_, fun s hs => by simpa [mul_comm] using hlin s 1 hs (map_one h.bar)⟩
  · rw [← hc₁, hχ, bar_miyamotoPairing]
  · intro v
    have hχs : ∀ s, h.bar s = s → χ s = χ 1 * s := fun s hs => by
      simpa [mul_comm] using hlin s 1 hs (map_one h.bar)
    rw [← sub_eq_zero]
    refine eq_zero_of_miyamotoPairing h fun w => ?_
    rw [miyamotoPairing_sub_left, ← hχ, miyamotoPairing_smul_left h ?_,
      hχs _ (bar_miyamotoPairing h v w), sub_self]
    rw [← hc₁, hχ, bar_miyamotoPairing]

theorem miyamotoPairing_semilinear (φ : (K × K) ≃+ (K × K)) (ψ ψ' : K → K)
    (hψ : ∀ v w, miyamotoPairing h (φ v) (φ w) = ψ (miyamotoPairing h v w))
    (hψ' : ∀ v w, miyamotoPairing h (φ.symm v) (φ.symm w) = ψ' (miyamotoPairing h v w)) :
    ∃ (σ : h.fixedField →+* h.fixedField) (μ : K), h.bar μ = μ ∧ μ ≠ 0 ∧
      ∀ s : h.fixedField, ψ s = μ * σ s := by
  have hcent : ∀ t : K, h.bar t = t → ∃ μ : K, h.bar μ = μ ∧
      ∀ u, φ (t • u) = μ • φ u := by
    intro t ht
    let θ : K × K →+ K × K := φ.toAddMonoidHom.comp
      ((DistribSMul.toAddMonoidHom (K × K) t).comp φ.symm.toAddMonoidHom)
    obtain ⟨μ, hμ, hθ, -⟩ := miyamotoPairing_centroid h θ (fun s => ψ (t * ψ' s)) fun v w => by
      rw [← hψ', ← miyamotoPairing_smul_left h ht, ← hψ]
      simp [θ]
    exact ⟨μ, hμ, fun u => by simpa [θ] using hθ (φ u)⟩
  set u₀ := φ.symm (1, 0)
  have hσ : ∀ t : K, h.bar t = t → h.bar (φ (t • u₀)).1 = (φ (t • u₀)).1 ∧
      ∀ u, φ (t • u) = (φ (t • u₀)).1 • φ u := by
    intro t ht
    obtain ⟨μ, hμ, hφμ⟩ := hcent t ht
    have e : (φ (t • u₀)).1 = μ := by
      rw [hφμ, show φ u₀ = (1, 0) from φ.apply_symm_apply _]
      simp
    rw [e]
    exact ⟨hμ, hφμ⟩
  let σ : h.fixedField →+* h.fixedField :=
    { toFun := fun t => ⟨(φ ((t : K) • u₀)).1, (hσ t t.2).1⟩
      map_one' := Subtype.ext (by
        change (φ ((1 : K) • u₀)).1 = 1
        rw [one_smul, φ.apply_symm_apply])
      map_mul' := fun t₁ t₂ => Subtype.ext (by
        change (φ (((t₁ : K) * t₂) • u₀)).1 = (φ ((t₁ : K) • u₀)).1 * (φ ((t₂ : K) • u₀)).1
        rw [mul_smul, (hσ t₁ t₁.2).2]
        rfl)
      map_zero' := Subtype.ext (by
        change (φ ((0 : K) • u₀)).1 = 0
        rw [zero_smul, map_zero]
        rfl)
      map_add' := fun t₁ t₂ => Subtype.ext (by
        change (φ (((t₁ : K) + t₂) • u₀)).1 = (φ ((t₁ : K) • u₀)).1 + (φ ((t₂ : K) • u₀)).1
        rw [add_smul, map_add]
        rfl) }
  have hψσ : ∀ t : h.fixedField, ∀ s : K, h.bar s = s →
      ψ ((t : K) * s) = (σ t : K) * ψ s := by
    intro t s hs
    obtain ⟨c', rfl⟩ := exists_miyamotoPairing_eq h hs
    rw [← miyamotoPairing_smul_left h t.2, ← hψ, ← hψ, (hσ t t.2).2,
      miyamotoPairing_smul_left h (hσ t t.2).1]
    rfl
  have hψψ : ∀ s : K, h.bar s = s → ψ' (ψ s) = s := by
    intro s hs
    obtain ⟨c', rfl⟩ := exists_miyamotoPairing_eq h hs
    rw [← hψ, ← hψ', φ.symm_apply_apply, φ.symm_apply_apply]
  obtain ⟨c₁, hc₁⟩ := exists_miyamotoPairing_eq h (map_one h.bar)
  refine ⟨σ, ψ 1, ?_, fun h0 => ?_, fun s => ?_⟩
  · rw [← hc₁, ← hψ, bar_miyamotoPairing]
  · have e1 := hψψ 1 (map_one h.bar)
    have e0 : ψ' 0 = 0 := by
      have := hψ' 0 0
      rw [miyamotoPairing_zero_left, map_zero, miyamotoPairing_zero_left] at this
      exact this.symm
    rw [h0, e0] at e1
    exact zero_ne_one e1
  · have := hψσ s 1 (map_one h.bar)
    rw [mul_one] at this
    rw [this, mul_comm]

end Centroid

section Group

variable [CharP K 2] {X : Type*} [Group X]

theorem map_commutator_eq_miyamotoZ (π : X →* GL (Fin 4) K) (hπ : π.range = miyamotoA2 h) :
    (commutator X).map π = miyamotoZ h := by
  rw [commutator_def, map_commutator, ← MonoidHom.range_eq_map, hπ, commutator_miyamotoA2]

theorem mulEquiv_apply_mem_center {θ : X ≃* X} {x : X} (hx : x ∈ center X) :
    θ x ∈ center X := by
  rw [mem_center_iff] at hx ⊢
  intro g
  have := congrArg θ (hx (θ.symm g))
  rwa [map_mul, map_mul, MulEquiv.apply_symm_apply] at this

theorem mulEquiv_apply_mem_commutator {θ : X ≃* X} {z : X} (hz : z ∈ commutator X) :
    θ z ∈ commutator X := by
  have := map_commutator (⊤ : Subgroup X) ⊤ θ.toMonoidHom
  rw [map_top_of_surjective _ θ.surjective] at this
  rw [commutator_def, ← this]
  exact ⟨z, hz, rfl⟩

theorem exists_semilinear_of_mulEquiv (π : X →* GL (Fin 4) K) (hπ : π.range = miyamotoA2 h)
    (hkerX : π.ker ⊓ commutator X = ⊥) (θ : X ≃* X) :
    ∃ (σ : h.fixedField →+* h.fixedField) (μ : K), h.bar μ = μ ∧ μ ≠ 0 ∧
      ∀ z ∈ commutator X, ∀ s : h.fixedField, π z = miyamotoXGL h 0 0 0 s →
        π (θ z) = miyamotoXGL h 0 0 0 (μ * σ s) := by
  classical
  have hbb := h.bar_bar
  have hmem : ∀ x : X, π x ∈ miyamotoA2 h := fun x => hπ ▸ (⟨x, rfl⟩ : π x ∈ π.range)
  let cA : X → K × K := fun x =>
    ((π x : Matrix (Fin 4) (Fin 4) K) 1 0, (π x : Matrix (Fin 4) (Fin 4) K) 2 0)
  have hcA : ∀ x : X, ∃ a c d : K, d + h.bar d + a * h.bar c + h.bar a * c = 0 ∧
      π x = miyamotoXGL h a 0 c d ∧ cA x = (a, c) := by
    intro x
    obtain ⟨a, c, d, hd, e⟩ := (mem_A2 h).1 (hmem x)
    refine ⟨a, c, d, hd, e, ?_⟩
    simp only [cA, e, coe_miyamotoXGL, miyamotoX_one_zero, miyamotoX_two_zero]
  have hcA_mul : ∀ x y : X, cA (x * y) = cA x + cA y := by
    intro x y
    obtain ⟨a, c, d, -, ex, hx⟩ := hcA x
    obtain ⟨a', c', d', -, ey, hy⟩ := hcA y
    have e : π (x * y) = miyamotoXGL h (a + a') 0 (c + c') (d + d' + h.bar c * a' +
        h.bar a * c') := by
      rw [map_mul, ex, ey, miyamotoXGL_mul h (map_zero _)]
      simp
    rw [hx, hy]
    simp only [cA, e, coe_miyamotoXGL, miyamotoX_one_zero, miyamotoX_two_zero, Prod.mk_add_mk]
  have hcA_one : cA 1 = 0 := by simp [cA]
  have hcA_inv : ∀ x : X, cA x⁻¹ = -cA x := by
    intro x
    have := hcA_mul x x⁻¹
    rw [mul_inv_cancel, hcA_one] at this
    exact eq_neg_of_add_eq_zero_right this.symm
  have hZ : ∀ x : X, x ∈ center X ↔ cA x = 0 := by
    intro x
    obtain ⟨a, c, d, hd, ex, hx⟩ := hcA x
    rw [hx]
    constructor
    · intro hxc
      have hxZ : π x ∈ miyamotoZ h := by
        rw [← centerIn_miyamotoA2 h]
        refine ⟨hmem x, mem_centralizer_iff.2 fun y hy => ?_⟩
        rw [← hπ] at hy
        obtain ⟨y', rfl⟩ := hy
        rw [← map_mul, ← map_mul, mem_center_iff.1 hxc y']
      rw [ex, miyamotoXGL_mem_Z] at hxZ
      rw [hxZ.1, hxZ.2.2.1]
      rfl
    · intro hac
      obtain ⟨rfl, rfl⟩ := Prod.mk.injEq _ _ _ _ ▸ hac
      have hxZ : π x ∈ miyamotoZ h :=
        ex ▸ (miyamotoXGL_mem_Z h).2 ⟨rfl, rfl, rfl,
          (add_bar_eq_zero_iff h).1 (by simpa using hd)⟩
      refine mem_center_iff.2 fun y => ?_
      have hc : ⁅x, y⁆ ∈ π.ker ⊓ commutator X := by
        refine mem_inf.2 ⟨MonoidHom.mem_ker.2 ?_,
          commutator_mem_commutator (mem_top x) (mem_top y)⟩
        rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
        exact (mem_centralizer_iff.1 ((centerIn_miyamotoP h).ge hxZ).2 _
          (miyamotoA2_le_P h (hmem y))).symm
      rw [hkerX, mem_bot, commutatorElement_eq_one_iff_mul_comm] at hc
      exact hc.symm
  have hθc : ∀ (θ' : X ≃* X) (x y : X), cA x = cA y → cA (θ' x) = cA (θ' y) := by
    intro θ' x y e
    have h1 : x⁻¹ * y ∈ center X := by
      rw [hZ, hcA_mul, hcA_inv, e, neg_add_cancel]
    have h2 := (hZ _).1 (mulEquiv_apply_mem_center (θ := θ') h1)
    rw [map_mul, map_inv, hcA_mul, hcA_inv, neg_add_eq_zero] at h2
    exact h2
  have hsec : ∀ v : K × K, ∃ x : X, cA x = v := by
    rintro ⟨a, c⟩
    have : miyamotoXGL h a 0 c (h.bar a * c) ∈ π.range := by
      rw [hπ, miyamotoXGL_mem_A2]
      refine ⟨rfl, ?_⟩
      simp only [map_mul, hbb]
      linear_combination (h.bar a * c + a * h.bar c) * CharTwo.two_eq_zero (R := K)
    obtain ⟨x, hx⟩ := this
    exact ⟨x, by simp [cA, hx]⟩
  choose sec hsec' using hsec
  have hZX : ∀ s : K, h.bar s = s → ∃ z ∈ commutator X, π z = miyamotoXGL h 0 0 0 s := by
    intro s hs
    have : miyamotoXGL h 0 0 0 s ∈ (commutator X).map π := by
      rw [map_commutator_eq_miyamotoZ h π hπ]
      exact ⟨s, hs, rfl⟩
    obtain ⟨z, hz, e⟩ := this
    exact ⟨z, hz, e⟩
  choose zs hzs hzs' using hZX
  have hinj : ∀ z ∈ commutator X, ∀ z' ∈ commutator X, π z = π z' → z = z' := by
    intro z hz z' hz' e
    have : z⁻¹ * z' ∈ π.ker ⊓ commutator X := mem_inf.2
      ⟨MonoidHom.mem_ker.2 (by rw [map_mul, map_inv, e, inv_mul_cancel]),
        (commutator X).mul_mem ((commutator X).inv_mem hz) hz'⟩
    rw [hkerX, mem_bot, inv_mul_eq_one] at this
    exact this
  have hcomm : ∀ x y : X,
      π ⁅x, y⁆ = miyamotoXGL h 0 0 0 (miyamotoPairing h (cA x) (cA y)) := by
    intro x y
    obtain ⟨a, c, d, -, ex, hx⟩ := hcA x
    obtain ⟨a', c', d', -, ey, hy⟩ := hcA y
    rw [map_commutatorElement, ex, ey, miyamotoXGL_commutator_A2_eq_pairing, hx, hy]
  have key : ∀ θ' : X ≃* X, ∃ (φ : K × K → K × K) (ψ : K → K),
      (∀ x, cA (θ' x) = φ (cA x)) ∧ (∀ v w, miyamotoPairing h (φ v) (φ w) =
        ψ (miyamotoPairing h v w)) ∧ ∀ z ∈ commutator X, ∀ s : K, h.bar s = s →
          π z = miyamotoXGL h 0 0 0 s → π (θ' z) = miyamotoXGL h 0 0 0 (ψ s) := by
    intro θ'
    let ψ : K → K := fun s => if hs : h.bar s = s then
      (π (θ' (zs s hs)) : Matrix (Fin 4) (Fin 4) K) 3 0 else 0
    have hψZ : ∀ z ∈ commutator X, ∀ s : K, h.bar s = s →
        π z = miyamotoXGL h 0 0 0 s → π (θ' z) = miyamotoXGL h 0 0 0 (ψ s) := by
      intro z hz s hs e
      have hz' : z = zs s hs := hinj z hz _ (hzs s hs) (e.trans (hzs' s hs).symm)
      have : π (θ' z) ∈ miyamotoZ h := by
        rw [← map_commutator_eq_miyamotoZ h π hπ]
        exact ⟨_, mulEquiv_apply_mem_commutator hz, rfl⟩
      obtain ⟨d, -, ed⟩ := this
      rw [ed]
      congr 1
      have : ψ s = (π (θ' (zs s hs)) : Matrix (Fin 4) (Fin 4) K) 3 0 := dite_eq_left hs
      rw [this, ← hz', ed, coe_miyamotoXGL, miyamotoX_three_zero]
    refine ⟨fun v => cA (θ' (sec v)), ψ, fun x => hθc θ' x (sec (cA x)) (hsec' _).symm,
      fun v w => ?_, hψZ⟩
    have hc := hψZ ⁅sec v, sec w⁆ (commutator_mem_commutator (mem_top _) (mem_top _))
      (miyamotoPairing h v w) (bar_miyamotoPairing h v w) (by rw [hcomm, hsec', hsec'])
    rw [map_commutatorElement, hcomm] at hc
    exact ((miyamotoXGL_inj h).1 hc).2.2.2
  obtain ⟨φ₁, ψ₁, hφ₁, hψ₁, hZ₁⟩ := key θ
  obtain ⟨φ₂, ψ₂, hφ₂, hψ₂, -⟩ := key θ.symm
  have h12 : ∀ v, φ₂ (φ₁ v) = v := fun v => by
    rw [← hsec' v, ← hφ₁, ← hφ₂, MulEquiv.symm_apply_apply]
  have h21 : ∀ v, φ₁ (φ₂ v) = v := fun v => by
    rw [← hsec' v, ← hφ₂, ← hφ₁, MulEquiv.apply_symm_apply]
  have hadd : ∀ v w, φ₁ (v + w) = φ₁ v + φ₁ w := fun v w => by
    rw [← hsec' v, ← hsec' w, ← hcA_mul, ← hφ₁, ← hφ₁, ← hφ₁, map_mul, hcA_mul]
  let φ : (K × K) ≃+ (K × K) :=
    { toFun := φ₁, invFun := φ₂, left_inv := h12, right_inv := h21, map_add' := hadd }
  obtain ⟨σ, μ, hμ, hμ0, hψ⟩ := miyamotoPairing_semilinear h φ ψ₁ ψ₂ hψ₁ hψ₂
  exact ⟨σ, μ, hμ, hμ0, fun z hz s e => by rw [hZ₁ z hz s s.2 e, hψ s]⟩

end Group

end CFSG.LocalAnalysis.EvenBN.U4
