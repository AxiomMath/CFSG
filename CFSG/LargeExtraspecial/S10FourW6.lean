module

public import CFSG.LargeExtraspecial.S10EightK
public import CFSG.LargeExtraspecial.S10FourN

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S10

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6

universe u

@[expose] def tvMap (b₀ b₁ b₂ b₃ : ZMod 2) (d x : M2) : M2 :=
  x + (b₀ * x 0 0 + b₁ * x 0 1 + b₂ * x 1 0 + b₃ * x 1 1) • d

set_option synthInstance.maxSize 2048 in
theorem no_refl_normalizing : ∀ d : M2, ∀ b₀ : ZMod 2, ∀ b₁ : ZMod 2, ∀ b₂ : ZMod 2,
    ∀ b₃ : ZMod 2,
    (∀ x : M2, qf (tvMap b₀ b₁ b₂ b₃ d x) = qf x) → (∃ x : M2, tvMap b₀ b₁ b₂ b₃ d x ≠ x) →
    ∀ δ : Gm, δ.1 = 1 → δ ≠ 1 → ∀ δ' : Gm, δ'.1 = 1 →
    (∀ x : M2, tvMap b₀ b₁ b₂ b₃ d (act δ x) = act δ' (tvMap b₀ b₁ b₂ b₃ d x)) → False := by
  decide +kernel

theorem M2_decomp : ∀ x : M2, x = x 0 0 • (!![1, 0; 0, 0] : M2) + x 0 1 • !![0, 1; 0, 0] +
    x 1 0 • !![0, 0; 1, 0] + x 1 1 • !![0, 0; 0, 1] := by
  decide

theorem exists_tvMap (T : M2 →ₗ[ZMod 2] M2) {d : M2}
    (hT : ∀ x, T x = x ∨ T x = x + d) :
    ∃ b₀ b₁ b₂ b₃ : ZMod 2, ∀ x, T x = tvMap b₀ b₁ b₂ b₃ d x := by
  have hb : ∀ e, ∃ b : ZMod 2, T e = e + b • d := fun e => by
    rcases hT e with h | h
    · exact ⟨0, by rw [h, zero_smul, add_zero]⟩
    · exact ⟨1, by rw [h, one_smul]⟩
  obtain ⟨b₀, h₀⟩ := hb !![1, 0; 0, 0]
  obtain ⟨b₁, h₁⟩ := hb !![0, 1; 0, 0]
  obtain ⟨b₂, h₂⟩ := hb !![0, 0; 1, 0]
  obtain ⟨b₃, h₃⟩ := hb !![0, 0; 0, 1]
  refine ⟨b₀, b₁, b₂, b₃, fun x => ?_⟩
  have e : T x = x 0 0 • T !![1, 0; 0, 0] + x 0 1 • T !![0, 1; 0, 0] +
      x 1 0 • T !![0, 0; 1, 0] + x 1 1 • T !![0, 0; 0, 1] := by
    conv_lhs => rw [M2_decomp x]
    simp only [map_add, map_smul]
  rw [e, h₀, h₁, h₂, h₃, tvMap]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> ring

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G} {t : S.O}

theorem DirDec.eq_or_eq_inv_of_mem_commutator {Xb Yb : Subgroup S.O} (D : DirDec S g t Xb Yb)
    {θ x : S.O} (hθ : θ ∈ ⁅Yb, Yb⁆) (hθ1 : θ ≠ 1) (hx : x ∈ ⁅Yb, Yb⁆) (hx1 : x ≠ 1) :
    x = θ ∨ x = θ⁻¹ := by
  have key : ∀ σ τ : Equiv.Perm (Fin 3), σ ^ 3 = 1 → σ ≠ 1 → τ ^ 3 = 1 → τ ≠ 1 →
      τ = σ ∨ τ = σ⁻¹ := by decide
  obtain ⟨e⟩ := D.iso
  obtain ⟨hθY, hθ3⟩ := D.mem_commutator_iff.1 hθ
  obtain ⟨hxY, hx3⟩ := D.mem_commutator_iff.1 hx
  set θ' : Yb := ⟨θ, hθY⟩
  set x' : Yb := ⟨x, hxY⟩
  have hθ3' : e θ' ^ 3 = 1 := by rw [← map_pow, show θ' ^ 3 = 1 from Subtype.ext hθ3, map_one]
  have hx3' : e x' ^ 3 = 1 := by rw [← map_pow, show x' ^ 3 = 1 from Subtype.ext hx3, map_one]
  have hθ1' : e θ' ≠ 1 := fun h => hθ1 (congrArg Subtype.val (e.map_eq_one_iff.1 h))
  have hx1' : e x' ≠ 1 := fun h => hx1 (congrArg Subtype.val (e.map_eq_one_iff.1 h))
  rcases key _ _ hθ3' hθ1' hx3' hx1' with h | h
  · exact Or.inl (congrArg Subtype.val (e.injective h))
  · refine Or.inr (congrArg Subtype.val (e.injective ?_) : (x' : S.O) = (θ'⁻¹ : Yb))
    rw [h, map_inv]

theorem StronglyClosedL.fix_Vt_of_conj_six (hSC : StronglyClosedL S g t)
    (hCE : CentralExtInput.{u}) (X : Hyp10 S g t) {Xb Yb : Subgroup S.O} (D : Dec108 X Xb Yb)
    (h6 : S.width = 6) {m : S.M} (hne : S.ρ m * t * (S.ρ m)⁻¹ ≠ t)
    (hcomm : (S.ρ m * t * (S.ρ m)⁻¹) * t = t * (S.ρ m * t * (S.ρ m)⁻¹)) :
    ∀ v ∈ Vt S g t, ((S.ρ m * t * (S.ρ m)⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v := by
  obtain ⟨F, hFY, -, -⟩ := D.exists_frame hCE
  obtain ⟨t', ht'⟩ : ∃ t' : S.O, t' = S.ρ m * t * (S.ρ m)⁻¹ := ⟨_, rfl⟩
  have ht'M : t' ∈ S.Mbar := ht' ▸ conj_mem_Mbar X m
  obtain ⟨y₀, hy₀⟩ := MonoidHom.mem_range.mp ht'M
  have hy₀t : S.ρ y₀ * t = t * S.ρ y₀ := by rw [hy₀, ht']; exact hcomm
  rw [← ht'] at hne hcomm ⊢
  have hTt : (t' : S.Qt ≃ₗ[ZMod 2] S.Qt) * (t : S.Qt ≃ₗ[ZMod 2] S.Qt) =
      (t : S.Qt ≃ₗ[ZMod 2] S.Qt) * (t' : S.Qt ≃ₗ[ZMod 2] S.Qt) := by
    rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, hcomm]
  obtain ⟨hTV, hTW⟩ := apply_mem_Vt_Wt_of_commute X hTt
  have hD1 : ∀ v ∈ Vt S g t, (t' : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v ∉ orbit S g t := by
    intro v hv hdo
    obtain ⟨k, hk, hdk⟩ := exists_of_mem_orbit hdo X.haQ
    have htk := mem_Lbar_mul_of_mem_Rbar X.H X.ht hk
    have hcs : S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹) ∈
        commSpace ((S.ρ m * t * (S.ρ m)⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) := by
      rw [← ht', ← hdk]
      exact sub_mem_commSpace _ v
    have ht'k := hSC.mem_Lbar_of_mem_commSpace_conj X F hcs
    have h1 : S.ρ 1 * t * (S.ρ 1)⁻¹ ∈ S.Lbar ((k : G) * g) := by
      rw [map_one, one_mul, inv_one, mul_one]
      exact htk
    have := hSC.conj_eq_conj ht'k h1
    rw [map_one, one_mul, inv_one, mul_one, ← ht'] at this
    exact hne this
  by_contra hcon
  push Not at hcon
  obtain ⟨v₀, hv₀, hv₀m⟩ := hcon
  obtain ⟨p, hp, hpm⟩ : ∃ p ∈ orbit S g t, (t' : S.Qt ≃ₗ[ZMod 2] S.Qt) p ≠ p := by
    by_contra h
    push Not at h
    apply hv₀m
    have hle : Vt S g t ≤ fixSpace (t' : S.Qt ≃ₗ[ZMod 2] S.Qt) := by
      rw [Vt_eq_span_orbit X.H X.ht, Submodule.span_le]
      intro q hq
      exact mem_fixSpace.mpr (h q hq)
    exact mem_fixSpace.mp (hle hv₀)
  have hpV : p ∈ Vt S g t := orbit_subset_Vt X.ht X.haQ hp
  have hTp := apply_mem_orbit_of_commute X ht'M hcomm hp
  obtain ⟨k₁, hk₁, e₁⟩ := exists_orbV_eq X (v := ⟨p, hpV⟩) hp
  obtain ⟨k₂, hk₂, e₂⟩ := exists_orbV_eq X (v := ⟨_, hTV p hpV⟩) hTp
  have hβ : beta X.H X.C X.ht X.ht1 X.hVQ (orbV X.haQ X.ht hk₁) (orbV X.haQ X.ht hk₂) = 1 := by
    set d : Vt S g t := ⟨_, sub_mem (hTV p hpV) hpV⟩ with hd
    have hd0 : d ≠ 0 := fun h => hpm (sub_eq_zero.mp (congrArg Subtype.val h))
    have hQd := F.qf_eq_one hd0 (hD1 p hpV)
    have hsum : orbV X.haQ X.ht hk₂ = orbV X.haQ X.ht hk₁ + d := by
      rw [e₁, e₂]
      exact Subtype.ext (by simp [hd])
    have hQ1 : qf (F.φ (orbV X.haQ X.ht hk₁)) = 0 := by
      rw [← F.mem_orbit_iff (orbV_ne_zero' X hk₁)]
      exact ⟨S.ρ k₁, hk₁, coe_orbV X.haQ X.ht hk₁⟩
    have hQ2 : qf (F.φ (orbV X.haQ X.ht hk₂)) = 0 := by
      rw [← F.mem_orbit_iff (orbV_ne_zero' X hk₂)]
      exact ⟨S.ρ k₂, hk₂, coe_orbV X.haQ X.ht hk₂⟩
    have h3 := F.qf_add' (orbV X.haQ X.ht hk₁) d
    rw [← hsum, hQ2, hQ1, hQd, zero_add] at h3
    have hβd : beta X.H X.C X.ht X.ht1 X.hVQ (orbV X.haQ X.ht hk₁) d = 1 := by
      rcases CFSG.RankThree.Literature.FSmith.zmod2_cases
        (beta X.H X.C X.ht X.ht1 X.hVQ (orbV X.haQ X.ht hk₁) d) with h | h
      · rw [h] at h3
        exact absurd h3 (by decide)
      · exact h
    rw [hsum, map_add, (beta_isAlt X.H X.C X.ht X.ht1 X.hVQ) _, zero_add, hβd]
  have hcl : S.cl (((y₀ * k₁ : S.M) : G) * g * S.z * (((y₀ * k₁ : S.M) : G) * g)⁻¹) =
      S.cl ((k₂ : G) * g * S.z * ((k₂ : G) * g)⁻¹) := by
    rw [← ρ_cl_conj_mul X, hy₀, ← coe_orbV' X hk₁, e₁, ← coe_orbV' X hk₂, e₂]
  have hyP : ∀ w ∈ S.clSub (S.QG ⊓ S.Qa ((k₁ : G) * g)) ⊓ Wt S g t,
      (t' : S.Qt ≃ₗ[ZMod 2] S.Qt) w ∈ S.clSub (S.QG ⊓ S.Qa ((k₂ : G) * g)) ⊓ Wt S g t := by
    intro w hw
    refine ⟨?_, hTW w hw.2⟩
    have h1 := apply_mem_clSub_Qa_mul (g := (k₁ : G) * g) y₀ hw.1
    rw [hy₀] at h1
    rwa [show (y₀ : G) * ((k₁ : G) * g) = ((y₀ * k₁ : S.M) : G) * g by
        rw [Subgroup.coe_mul, mul_assoc],
      clSub_eq_of_cl_eq (conj_mem_QG' S (y₀ * k₁).2 X.haQ)
        (conj_ne_z' S (y₀ * k₁).2 X.H.conj_ne) (conj_mem_QG' S k₂.2 X.haQ) hcl] at h1
  have hsw := width_le_of_swap hCE X hk₁ hk₂ hβ hTV hyP
  have hflag := flag_of_commute X hTt
  rw [ht', finrank_commSpace_conj_t X m, ← ht'] at hflag
  have hK1 : finrank (ZMod 2) ((Vt S g t).map
      (((t' : S.Qt ≃ₗ[ZMod 2] S.Qt) : S.Qt →ₗ[ZMod 2] S.Qt) - 1)) ≤ 1 := by omega
  obtain ⟨K, hK⟩ : ∃ K : Submodule (ZMod 2) S.Qt,
      K = (Vt S g t).map (((t' : S.Qt ≃ₗ[ZMod 2] S.Qt) : S.Qt →ₗ[ZMod 2] S.Qt) - 1) := ⟨_, rfl⟩
  rw [← hK] at hK1
  obtain ⟨d, hd⟩ : ∃ d : S.Qt, d = (t' : S.Qt ≃ₗ[ZMod 2] S.Qt) p - p := ⟨_, rfl⟩
  have hdK : d ∈ K := by rw [hK, hd]; exact ⟨p, hpV, rfl⟩
  have hd0 : d ≠ 0 := fun h => hpm (sub_eq_zero.mp (hd ▸ h))
  have hKd : ∀ v ∈ Vt S g t, (t' : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v ∨
      (t' : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v + d := by
    intro v hv
    have hvK : (t' : S.Qt ≃ₗ[ZMod 2] S.Qt) v - v ∈ K := by rw [hK]; exact ⟨v, hv, rfl⟩
    have hspan : K = (ZMod 2) ∙ d := by
      refine (Submodule.eq_of_le_of_finrank_le ((Submodule.span_singleton_le_iff_mem _ _).2 hdK)
        ?_).symm
      rw [finrank_span_singleton hd0]
      exact hK1
    rw [hspan] at hvK
    rcases mem_span_singleton_zmod2.mp hvK with h | h
    · exact Or.inl (sub_eq_zero.mp h)
    · exact Or.inr (by rw [← h]; abel)
  obtain ⟨tV, htV⟩ : ∃ tV : Vt S g t →ₗ[ZMod 2] Vt S g t,
      ∀ v : Vt S g t, (tV v : S.Qt) = (t' : S.Qt ≃ₗ[ZMod 2] S.Qt) v :=
    ⟨((t' : S.Qt ≃ₗ[ZMod 2] S.Qt) : S.Qt →ₗ[ZMod 2] S.Qt).restrict hTV, fun v => rfl⟩
  obtain ⟨T, hTx⟩ : ∃ T : M2 →ₗ[ZMod 2] M2, ∀ v : Vt S g t, T (F.φ v) = F.φ (tV v) :=
    ⟨F.φ.toLinearMap ∘ₗ tV ∘ₗ F.φ.symm.toLinearMap, fun v => by simp⟩
  have hdV : d ∈ Vt S g t := hd ▸ sub_mem (hTV p hpV) hpV
  have hT : ∀ x, T x = x ∨ T x = x + F.φ ⟨d, hdV⟩ := by
    intro x
    obtain ⟨v, rfl⟩ := F.φ.surjective x
    rw [hTx]
    rcases hKd v v.2 with h | h
    · exact Or.inl (congrArg F.φ (Subtype.ext (by rw [htV]; exact h)))
    · refine Or.inr ?_
      rw [← map_add]
      exact congrArg F.φ (Subtype.ext (by rw [htV, Submodule.coe_add]; exact h))
  obtain ⟨b₀, b₁, b₂, b₃, hTb⟩ := exists_tvMap T hT
  have ht't' : t' * t' = 1 := by
    rw [ht']
    have htt := mul_self_of_mem_Lbar S X.H.conj_mem X.ht
    calc S.ρ m * t * (S.ρ m)⁻¹ * (S.ρ m * t * (S.ρ m)⁻¹) = S.ρ m * (t * t) * (S.ρ m)⁻¹ := by
          group
      _ = 1 := by rw [htt]; group
  have hinvol : ∀ v : S.Qt, (t' : S.Qt ≃ₗ[ZMod 2] S.Qt) ((t' : S.Qt ≃ₗ[ZMod 2] S.Qt) v) = v :=
    fun v => by rw [← LinearEquiv.mul_apply, ← Subgroup.coe_mul, ht't']; rfl
  have hqf : ∀ x, qf (T x) = qf x := by
    intro x
    obtain ⟨v, rfl⟩ := F.φ.surjective x
    rw [hTx]
    by_cases hv0 : v = 0
    · rw [hv0, map_zero, map_zero]
    have htv0 : tV v ≠ 0 := fun h => hv0 (Subtype.ext (by
      have := congrArg (fun w : Vt S g t => (t' : S.Qt ≃ₗ[ZMod 2] S.Qt) w) h
      simpa [htV, hinvol] using this))
    have hiff : (tV v : S.Qt) ∈ orbit S g t ↔ (v : S.Qt) ∈ orbit S g t := by
      rw [htV]
      refine ⟨fun h => ?_, fun h => apply_mem_orbit_of_commute X ht'M hcomm h⟩
      have := apply_mem_orbit_of_commute X ht'M hcomm h
      rwa [hinvol] at this
    rw [F.mem_orbit_iff htv0, F.mem_orbit_iff hv0] at hiff
    rcases CFSG.RankThree.Literature.FSmith.zmod2_cases (qf (F.φ v)) with h | h
    · rw [h, hiff.2 h]
    · rcases CFSG.RankThree.Literature.FSmith.zmod2_cases (qf (F.φ (tV v))) with h' | h'
      · rw [hiff.1 h'] at h
        exact absurd h (by decide)
      · rw [h, h']
  obtain ⟨⟨θ, hθ⟩, hθ1'⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp D.dec.commutator_ne_bot
  have hθ1 : θ ≠ 1 := fun h => hθ1' (Subtype.ext h)
  have hθR : θ ∈ Rbar S g t := D.dec.le_Rbar_right ((D.dec.mem_commutator_iff).1 hθ).1
  obtain ⟨hπ1, hπ3, hπne⟩ := D.dec.pi_spec hCE hFY hθ hθ1
  have hconj := D.conj_mem_commutator_of_commute hCE hy₀t hθ
  have hne1 : S.ρ y₀ * θ * (S.ρ y₀)⁻¹ ≠ 1 := fun h => hθ1 (by
    calc θ = (S.ρ y₀)⁻¹ * (S.ρ y₀ * θ * (S.ρ y₀)⁻¹) * S.ρ y₀ := by group
      _ = 1 := by rw [h]; group)
  have hφθ : ∀ (r : S.O) (hr : r ∈ Rbar S g t) (v : Vt S g t),
      F.φ ⟨(r : S.Qt ≃ₗ[ZMod 2] S.Qt) v, apply_mem_Vt_of_mem_Rbar X.haQ hr v.2⟩ =
        act (F.π ⟨r, hr⟩) (F.φ v) := fun r hr v => F.compat ⟨r, hr⟩ v
  have hnorm : ∀ (ε : S.O) (hε : ε ∈ Rbar S g t), t' * θ = ε * t' →
      ∀ x, T (act (F.π ⟨θ, hθR⟩) x) = act (F.π ⟨ε, hε⟩) (T x) := by
    intro ε hε hεt x
    obtain ⟨v, rfl⟩ := F.φ.surjective x
    rw [← hφθ θ hθR v, hTx, hTx, ← hφθ ε hε]
    congr 1
    apply Subtype.ext
    rw [htV]
    change (t' : S.Qt ≃ₗ[ZMod 2] S.Qt) ((θ : S.Qt ≃ₗ[ZMod 2] S.Qt) v) =
      (ε : S.Qt ≃ₗ[ZMod 2] S.Qt) ((tV v : Vt S g t) : S.Qt)
    rw [htV, ← LinearEquiv.mul_apply, ← LinearEquiv.mul_apply, ← Subgroup.coe_mul,
      ← Subgroup.coe_mul, hεt]
  have hmoved : ∃ x : M2, tvMap b₀ b₁ b₂ b₃ (F.φ ⟨d, hdV⟩) x ≠ x := by
    refine ⟨F.φ ⟨p, hpV⟩, ?_⟩
    rw [← hTb, hTx]
    intro h'
    have h2 : (tV ⟨p, hpV⟩ : S.Qt) = p := congrArg Subtype.val (F.φ.injective h')
    rw [htV] at h2
    exact hpm h2
  have hqf' : ∀ x, qf (tvMap b₀ b₁ b₂ b₃ (F.φ ⟨d, hdV⟩) x) = qf x := fun x => by
    rw [← hTb]
    exact hqf x
  obtain ⟨ε, hεY, hε1, hεt⟩ : ∃ ε ∈ ⁅Yb, Yb⁆, ε ≠ 1 ∧ t' * θ = ε * t' := by
    refine ⟨S.ρ y₀ * θ * (S.ρ y₀)⁻¹, hconj, hne1, ?_⟩
    rw [← hy₀]
    group
  have hεR : ε ∈ Rbar S g t := D.dec.le_Rbar_right ((D.dec.mem_commutator_iff).1 hεY).1
  obtain ⟨hπε, -, -⟩ := D.dec.pi_spec hCE hFY hεY hε1
  have hn := hnorm ε hεR hεt
  exact no_refl_normalizing (F.φ ⟨d, hdV⟩) b₀ b₁ b₂ b₃ hqf' hmoved (F.π ⟨θ, hθR⟩) hπ1 hπne
    (F.π ⟨ε, hεR⟩) hπε fun x => by rw [← hTb, ← hTb]; exact hn x

theorem timmesfeld_10_4_six (hCE : CentralExtInput.{u}) (X : Hyp10 S g t) {Xb Yb : Subgroup S.O}
    (D : Dec108 X Xb Yb) (h6 : S.width = 6) :
    ∃ k : S.M, S.ρ k * t * (S.ρ k)⁻¹ ∈ S.Lbar g ∧ S.ρ k * t * (S.ρ k)⁻¹ ≠ t :=
  timmesfeld_10_4_self_of_fix hCE X fun hSC _ hne hcomm =>
    hSC.fix_Vt_of_conj_six hCE X D h6 hne hcomm

end CFSG.LargeExtraspecial.S10
