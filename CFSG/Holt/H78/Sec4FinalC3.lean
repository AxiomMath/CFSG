module

public import CFSG.Holt.H78.Sec4FinalC2

public section


namespace CFSG.Holt.H78

open MulAction CFSG.Holt CFSG.Holt.General CFSG.Open
open CFSG.GH74.Uniqueness.Bender (rootCenter)
open scoped Pointwise

namespace FinConfig

section Lemma51

variable {G : Type} [Group G] [Finite G] {Ω : Type} [Fintype Ω] [DecidableEq Ω] [MulAction G Ω]
  [FaithfulSMul G Ω] {α β : Ω} {v : G} (C : FinConfig G Ω α β v)

include C in
theorem fixSet_eq_of_isConj_of_commute' (hS : Sec4Setting G Ω) {u s : G} (hu : IsConj v u)
    (hs : IsConj v s) (hus : Commute u s) {a b : Ω} (hab : a ≠ b)
    (ha : a ∈ fixSet Ω (Subgroup.zpowers s)) (hau : a ∈ fixSet Ω (Subgroup.zpowers u))
    (hb : b ∈ fixSet Ω (Subgroup.zpowers s)) (hbu : b ∈ fixSet Ω (Subgroup.zpowers u)) :
    fixSet Ω (Subgroup.zpowers s) = fixSet Ω (Subgroup.zpowers u) := by
  obtain ⟨g, rfl⟩ := isConj_iff.mp hu
  have hs' : IsConj v (g⁻¹ * s * g) := hs.trans (isConj_iff.mpr ⟨g⁻¹, by rw [inv_inv]⟩)
  have hvs' : Commute v (g⁻¹ * s * g) := by
    show v * (g⁻¹ * s * g) = g⁻¹ * s * g * v
    calc v * (g⁻¹ * s * g) = g⁻¹ * ((g * v * g⁻¹) * s) * g := by group
      _ = g⁻¹ * (s * (g * v * g⁻¹)) * g := by rw [hus.eq]
      _ = g⁻¹ * s * g * v := by group
  have hF' : fixSet Ω (Subgroup.zpowers (g⁻¹ * s * g)) = g⁻¹ • fixSet Ω (Subgroup.zpowers s) := by
    rw [show g⁻¹ * s * g = g⁻¹ * s * g⁻¹⁻¹ by rw [inv_inv], fixSet_zpowers_conj]
  have hFu := fixSet_zpowers_conj (Ω := Ω) g v
  have hmem : ∀ {c : Ω}, c ∈ fixSet Ω (Subgroup.zpowers s) →
      c ∈ fixSet Ω (Subgroup.zpowers (g * v * g⁻¹)) →
        g⁻¹ • c ∈ fixSet Ω (Subgroup.zpowers (g⁻¹ * s * g)) ∧
          g⁻¹ • c ∈ fixSet Ω (Subgroup.zpowers v) := fun {c} hcs hcu => by
    rw [hF']
    rw [hFu] at hcu
    exact ⟨Set.smul_mem_smul_set hcs, Set.mem_smul_set_iff_inv_smul_mem.mp hcu⟩
  obtain ⟨ha1, ha2⟩ := hmem ha hau
  obtain ⟨hb1, hb2⟩ := hmem hb hbu
  have key := C.fixSet_eq_of_isConj_of_commute hS hs' hvs'
    (fun h => hab (smul_left_cancel _ h)) ha1 ha2 hb1 hb2
  rw [hF', inv_smul_eq_iff] at key
  rw [key, hFu]

theorem not_isConj_x_mul (hS : Sec4Setting G Ω) (D : C.Splitting hS) {T : Subgroup G}
    (hT : fusionIsSylowIn 2 T
      (Subgroup.centralizer ((Subgroup.zpowers v : Subgroup G) : Set G)))
    (hUT : D.U ⊔ C.Y ≤ T) (hxv : IsConj v C.x) {p : G}
    (hp : p ∈ T ⊓ fixingSubgroup G (fixSet Ω (Subgroup.zpowers v))) (hp2 : p * p = 1)
    (hpZ : p ∉ C.Z) : ¬ IsConj v (C.x * p) := by
  intro hxp
  have hpP := (Subgroup.mem_inf.mp hp).2
  have hpp := C.fixingSubgroup_le_pair hpP
  have hpst := C.fixingSubgroup_le_stabilizer_inf hpP
  have hpN : C.psi ⟨p, hpp⟩ ∉ C.N := fun hN =>
    hpZ (C.mem_Z_of_psi_mem_N hS hT.2.1.to_inf_left inf_le_right (C.Z_le_inf hS D hUT) hp hp2 hN)
  have hψ2 : C.psi ⟨p, hpp⟩ * C.psi ⟨p, hpp⟩ = 1 := by
    rw [← C.psi_mul hpp hpp, show (⟨p * p, mul_mem hpp hpp⟩ : stabilizer G ({α, β} : Set Ω)) = 1
      from Subtype.ext hp2, map_one]
  have h3 := C.isNaturalSE_N.three_le_ncard_fixedBy (C.psi_mem_normalizer _) hψ2 hpN
  obtain ⟨c₁, hc₁⟩ := Set.nonempty_of_ncard_ne_zero (s := fixedBy C.Psi (C.psi ⟨p, hpp⟩))
    (by omega)
  obtain ⟨c₂, hc₂, hc₂₁⟩ :=
    Set.exists_ne_of_one_lt_ncard (s := fixedBy C.Psi (C.psi ⟨p, hpp⟩)) (by omega) c₁
  have hcxp := C.commute_of_mem_V hS D hT hUT D.x_mem_V hp
  have hfix : ∀ c : C.Psi, C.psi ⟨p, hpp⟩ c = c → ∃ σ : holtDelta G Ω α β,
      C.D.coord σ C.i₀ = c ∧ C.x • (σ : Ω) = σ ∧ p • (σ : Ω) = σ := by
    intro c hc
    obtain ⟨σ, ⟨hσc, hσx⟩, hu⟩ := C.existsUnique_fixed_x hS c
    refine ⟨σ, hσc, hσx, ?_⟩
    have hpσ := smul_mem_holtDelta_of_mem_inf hpst σ.2
    have h1 := hu ⟨p • (σ : Ω), hpσ⟩ ⟨?_, ?_⟩
    · exact congrArg Subtype.val h1
    · have h2 := C.psi_coord ⟨p, hpp⟩ σ
      rw [hσc, hc] at h2
      exact h2.symm
    · show C.x • p • (σ : Ω) = p • (σ : Ω)
      rw [← mul_smul, hcxp, mul_smul, hσx]
  obtain ⟨σ₁, hσ₁c, hσ₁x, hσ₁p⟩ := hfix c₁ hc₁
  obtain ⟨σ₂, hσ₂c, hσ₂x, hσ₂p⟩ := hfix c₂ hc₂
  have hσne : (σ₁ : Ω) ≠ σ₂ := fun h => hc₂₁ (by
    rw [← hσ₁c, ← hσ₂c, show σ₁ = σ₂ from Subtype.ext h])
  have hmemF : ∀ {g : G} {ω : Ω}, g • ω = ω → ω ∈ fixSet Ω (Subgroup.zpowers g) := fun h => by
    rw [fixSet_zpowers, mem_fixedBy]
    exact h
  have hxpσ : ∀ {σ : Ω}, C.x • σ = σ → p • σ = σ → (C.x * p) • σ = σ := fun h1 h2 => by
    rw [mul_smul, h2, h1]
  have hcomm : Commute C.x (C.x * p) := by
    show C.x * (C.x * p) = C.x * p * C.x
    rw [mul_assoc, ← hcxp]
  have hF := C.fixSet_eq_of_isConj_of_commute' hS hxv hxp hcomm hσne
    (hmemF (hxpσ hσ₁x hσ₁p)) (hmemF hσ₁x) (hmemF (hxpσ hσ₂x hσ₂p)) (hmemF hσ₂x)
  obtain ⟨g, hg⟩ := isConj_iff.mp hxv
  have hx2 := C.x_mul_self hS
  set t := g⁻¹ * (C.x * p) * g with ht_def
  have ht : IsConj v t := hxp.trans (isConj_iff.mpr ⟨g⁻¹, by rw [inv_inv]⟩)
  have hFt : fixSet Ω (Subgroup.zpowers t) = fixSet Ω (Subgroup.zpowers v) := by
    rw [ht_def, show g⁻¹ * (C.x * p) * g = g⁻¹ * (C.x * p) * g⁻¹⁻¹ by rw [inv_inv],
      fixSet_zpowers_conj, hF, ← hg, fixSet_zpowers_conj, inv_smul_smul]
  have htP : t ∈ fixingSubgroup G (fixSet Ω (Subgroup.zpowers v)) :=
    (mem_fixingSubgroup_iff G).mpr fun ω hω => by
      rw [← hFt, fixSet_zpowers, mem_fixedBy] at hω
      exact hω
  have hvt : Commute v t := by
    show v * t = t * v
    have hv : v = g⁻¹ * C.x * g := by rw [← hg]; group
    rw [hv, ht_def]
    calc g⁻¹ * C.x * g * (g⁻¹ * (C.x * p) * g) = g⁻¹ * (C.x * (C.x * p)) * g := by group
      _ = g⁻¹ * (C.x * p * C.x) * g := by rw [hcomm.eq]
      _ = g⁻¹ * (C.x * p) * g * (g⁻¹ * C.x * g) := by group
  have hp1 : p ≠ 1 := fun h => hpZ (h ▸ one_mem _)
  have hne : v ≠ t := fun h => hp1 (by
    have h1 : C.x * p = C.x := by
      calc C.x * p = g * t * g⁻¹ := by rw [ht_def]; group
        _ = C.x := by rw [← h, hg]
    exact mul_eq_left.mp h1)
  have hvtF := (C.isConj_mul_of_mem_fixingSubgroup hS ht htP hvt hne).2
  have hvt_eq : v * t = g⁻¹ * p * g := by
    have hv : v = g⁻¹ * C.x * g := by rw [← hg]; group
    rw [hv, ht_def]
    calc g⁻¹ * C.x * g * (g⁻¹ * (C.x * p) * g) = g⁻¹ * ((C.x * C.x) * p) * g := by group
      _ = g⁻¹ * p * g := by rw [hx2, one_mul]
  rw [hvt_eq, show g⁻¹ * p * g = g⁻¹ * p * g⁻¹⁻¹ by rw [inv_inv], fixSet_zpowers_conj,
    inv_smul_eq_iff, ← fixSet_zpowers_conj, hg] at hvtF
  obtain ⟨δ, hδΦ, hδγ⟩ := C.exists_mem_fixSet_ne_γ
  have hδp : δ ∈ fixSet Ω (Subgroup.zpowers p) := hmemF ((mem_fixingSubgroup_iff G).mp hpP δ hδΦ)
  rw [hvtF, fixSet_zpowers, mem_fixedBy] at hδp
  exact hδγ (C.eq_γ_of_mem_fixSet_of_x_smul hS hδΦ hδp)

theorem mem_Z_or_mem_V (hS : Sec4Setting G Ω) (D : C.Splitting hS) {T : Subgroup G}
    (hT : fusionIsSylowIn 2 T
      (Subgroup.centralizer ((Subgroup.zpowers v : Subgroup G) : Set G)))
    (hUT : D.U ⊔ C.Y ≤ T) (hxv : IsConj v C.x) {s : G} (hs : IsConj v s) (hsT : s ∈ T) :
    s ∈ C.Z ∨ s ∈ D.V := by
  rcases C.isConj_shape hS D hT hUT hs hsT with h | h | ⟨r, hr, hr1, p, hp, hp2, hpZ, rfl⟩
  · exact Or.inl h
  · exact Or.inr h
  · exfalso
    have hx1 : C.x ≠ 1 := fun h => C.ne (by
      have h1 := (C.x_smul hS).1
      rwa [h, one_smul] at h1)
    exact C.not_isConj_x_mul hS D hT hUT hxv hp hp2 hpZ
      (C.isConj_mul_of_isConj_mul hS D hT hUT hr hr1 hp hp2 hpZ D.x_mem_V hx1 hp hp2 hpZ hs)

end Lemma51

section Theorem52

variable {G : Type} [Group G] [Finite G] {Ω : Type} [Fintype Ω] [DecidableEq Ω] [MulAction G Ω]
  [FaithfulSMul G Ω] {α β : Ω} {v : G} (C : FinConfig G Ω α β v)

theorem commute_x_of_mem_U (hS : Sec4Setting G Ω) (D : C.Splitting hS) {u : G} (hu : u ∈ D.U) :
    C.x * u = u * C.x := by
  have hxU := D.V_le D.x_mem_V
  have hk : C.x * u * C.x⁻¹ * u⁻¹ ∈ D.U :=
    mul_mem (mul_mem (mul_mem hxU hu) (inv_mem hxU)) (inv_mem hu)
  have hxC := C.centralizer_Y_le hS (D.Mc_le (D.U_le hxU))
  have huC := C.centralizer_Y_le hS (D.Mc_le (D.U_le hu))
  have hxR := D.piM_U_mem C.x hxU
  have huR := D.piM_U_mem u hu
  obtain ⟨hM, h2, -, hγ⟩ := C.piM_x hS
  have hxZ : C.piM hS ⟨C.x, hxC⟩ ∈ rootCenter (seRadical (C.Dv.M C.i)
      (C.Dv.coord ⟨C.γ, C.γ_mem⟩ C.i)) :=
    (C.isNaturalSE_Dv C.i).mem_rootCenter_seRadical hM hγ (by
      rw [← map_mul, show (⟨C.x, hxC⟩ : Subgroup.centralizer
        ((Subgroup.zpowers v : Subgroup G) : Set G)) * ⟨C.x, hxC⟩ = 1 from
          Subtype.ext (C.x_mul_self hS), map_one])
  have hc : C.piM hS ⟨C.x, hxC⟩ * C.piM hS ⟨u, huC⟩ = C.piM hS ⟨u, huC⟩ * C.piM hS ⟨C.x, hxC⟩ :=
    ((Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hxZ).2) _ huR).symm
  have h1 := D.piM_eq_one _ hk (by
    rw [show (⟨C.x * u * C.x⁻¹ * u⁻¹, C.centralizer_Y_le hS (D.Mc_le (D.U_le hk))⟩ :
      Subgroup.centralizer ((Subgroup.zpowers v : Subgroup G) : Set G)) =
        ⟨C.x, hxC⟩ * ⟨u, huC⟩ * ⟨C.x, hxC⟩⁻¹ * ⟨u, huC⟩⁻¹ from rfl, map_mul, map_mul, map_mul,
      map_inv, map_inv, hc, mul_inv_cancel_right, mul_inv_cancel])
  calc C.x * u = (C.x * u * C.x⁻¹ * u⁻¹) * u * C.x := by group
    _ = u * C.x := by rw [h1, one_mul]

theorem U_sup_Z_le_centralizer_x (hS : Sec4Setting G Ω) (D : C.Splitting hS) :
    D.U ⊔ C.Z ≤ Subgroup.centralizer ((Subgroup.zpowers C.x : Subgroup G) : Set G) := by
  refine sup_le (fun u hu => mem_centralizer_zpowers (C.commute_x_of_mem_U hS D hu)) fun z hz =>
    mem_centralizer_zpowers (C.commute_x hS (C.Z_le_Y hz))

theorem isPGroup_U_sup_Z (hS : Sec4Setting G Ω) (D : C.Splitting hS) :
    IsPGroup 2 ↥(D.U ⊔ C.Z) :=
  D.sylow.2.1.to_sup_of_normal_right' (C.sylow.2.1.to_le (C.Z_le_Y.trans C.Y_le_S))
    ((D.U_le.trans D.Mc_le).trans ((Subgroup.centralizer_le C.Z_le_Y).trans
      (Subgroup.centralizer_le_normalizer _)))

theorem isConj_of_mem_V (hS : Sec4Setting G Ω) (D : C.Splitting hS) (hxv : IsConj v C.x)
    {r : G} (hr : r ∈ D.V) (hr1 : r ≠ 1) : IsConj v r := by
  obtain ⟨h, -, rfl⟩ := D.exists_conj_x r hr hr1
  exact hxv.trans (isConj_iff.mpr ⟨h, rfl⟩)

theorem eq_one_of_mem_V_of_mem_Z (hS : Sec4Setting G Ω) (D : C.Splitting hS) {r : G}
    (hr : r ∈ D.V) (hrZ : r ∈ C.Z) : r = 1 :=
  D.piM_eq_one r (D.V_le hr) ((C.piM_eq_one_iff hS _).mpr fun _ hω =>
    C.smul_eq_of_mem_Z_of_mem_fixSet hS hrZ hω)

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem fixSet_zpowers_conj_inv (g y : G) :
    fixSet Ω (Subgroup.zpowers (g⁻¹ * y * g)) = g⁻¹ • fixSet Ω (Subgroup.zpowers y) := by
  rw [show g⁻¹ * y * g = g⁻¹ * y * g⁻¹⁻¹ by rw [inv_inv], fixSet_zpowers_conj]

theorem fixSet_ne_fixSet_x (hS : Sec4Setting G Ω) :
    fixSet Ω (Subgroup.zpowers v) ≠ fixSet Ω (Subgroup.zpowers C.x) := fun h => by
  obtain ⟨δ, hδΦ, hδγ⟩ := C.exists_mem_fixSet_ne_γ
  have hδx : δ ∈ fixSet Ω (Subgroup.zpowers C.x) := h ▸ hδΦ
  rw [fixSet_zpowers, mem_fixedBy] at hδx
  exact hδγ (C.eq_γ_of_mem_fixSet_of_x_smul hS hδΦ hδx)

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
theorem conj_ne_one {g y : G} (hy : y ≠ 1) : g⁻¹ * y * g ≠ 1 := fun h => hy (by
  calc y = g * (g⁻¹ * y * g) * g⁻¹ := by group
    _ = 1 := by rw [h]; group)

theorem fixSet_eq_of_mem_V (hS : Sec4Setting G Ω) (D : C.Splitting hS) {T : Subgroup G}
    (hT : fusionIsSylowIn 2 T
      (Subgroup.centralizer ((Subgroup.zpowers v : Subgroup G) : Set G)))
    (hUT : D.U ⊔ C.Y ≤ T) (hxv : IsConj v C.x) {r : G} (hr : r ∈ D.V) (hr1 : r ≠ 1) :
    fixSet Ω (Subgroup.zpowers r) = fixSet Ω (Subgroup.zpowers C.x) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g₀, hg₀⟩ := isConj_iff.mp hxv
  set A := (D.U ⊔ C.Z).map (MulAut.conj g₀⁻¹).toMonoidHom
  have hA2 : IsPGroup 2 A := (C.isPGroup_U_sup_Z hS D).map _
  have hAC : A ≤ Subgroup.centralizer ((Subgroup.zpowers v : Subgroup G) : Set G) := by
    rintro _ ⟨w, hw, rfl⟩
    have hwx : C.x * w = w * C.x :=
      Subgroup.mem_centralizer_iff.mp (C.U_sup_Z_le_centralizer_x hS D hw) C.x
        (Subgroup.mem_zpowers _)
    refine mem_centralizer_zpowers ?_
    show v * ((MulAut.conj g₀⁻¹).toMonoidHom w) = (MulAut.conj g₀⁻¹).toMonoidHom w * v
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    have hv : v = g₀⁻¹ * C.x * g₀ := by rw [← hg₀]; group
    rw [hv]
    calc g₀⁻¹ * C.x * g₀ * (g₀⁻¹ * w * g₀) = g₀⁻¹ * (C.x * w) * g₀ := by group
      _ = g₀⁻¹ * (w * C.x) * g₀ := by rw [hwx]
      _ = g₀⁻¹ * w * g₀ * (g₀⁻¹ * C.x * g₀) := by group
  obtain ⟨T₁, hAT₁, hT₁⟩ := exists_fusionIsSylowIn_ge hA2 hAC
  obtain ⟨c, hcC, hc⟩ := exists_mem_conj_of_fusionIsSylowIn hT hT₁
  set g := g₀ * c with hg_def
  have key : ∀ {w : G}, w ∈ D.U ⊔ C.Z → IsConj v w →
      g⁻¹ * w * g ∈ C.Z ∨ g⁻¹ * w * g ∈ D.V := by
    intro w hw hwv
    have h1 : g₀⁻¹ * w * g₀ ∈ T₁ :=
      hAT₁ ⟨w, hw, by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]⟩
    have h2 : c⁻¹ * (g₀⁻¹ * w * g₀) * c ∈ T := (hc _).mp h1
    have h3 : IsConj v (c⁻¹ * (g₀⁻¹ * w * g₀) * c) :=
      hwv.trans (isConj_iff.mpr ⟨c⁻¹ * g₀⁻¹, by group⟩)
    rw [show g⁻¹ * w * g = c⁻¹ * (g₀⁻¹ * w * g₀) * c by rw [hg_def]; group]
    exact C.mem_Z_or_mem_V hS D hT hUT hxv h3 h2
  have hgΦ : g • fixSet Ω (Subgroup.zpowers v) = fixSet Ω (Subgroup.zpowers C.x) := by
    rw [hg_def, mul_smul, smul_fixSet_zpowers_of_mem_centralizer hcC, ← fixSet_zpowers_conj, hg₀]
  have hZF : ∀ {w : G}, g⁻¹ * w * g ∈ C.Z → w ≠ 1 →
      fixSet Ω (Subgroup.zpowers w) = fixSet Ω (Subgroup.zpowers C.x) := fun {w} hw hw1 => by
    have hF := C.fixSet_eq_of_mem_Z hS hw (conj_ne_one hw1)
    rw [fixSet_zpowers_conj_inv, inv_smul_eq_iff] at hF
    rw [hF, hgΦ]
  have hvV : g⁻¹ * v * g ∈ D.V := by
    rcases key (Subgroup.mem_sup_right (C.v_mem_Z hS)) (IsConj.refl v) with h | h
    · exact absurd (hZF h C.v_ne_one) (C.fixSet_ne_fixSet_x hS)
    · exact h
  by_contra hne
  have hrV : g⁻¹ * r * g ∈ D.V := by
    rcases key (Subgroup.mem_sup_left (D.V_le hr)) (C.isConj_of_mem_V hS D hxv hr hr1) with h | h
    · exact absurd (hZF h hr1) hne
    · exact h
  have hrvV : g⁻¹ * (r * v) * g ∈ D.V := by
    rw [show g⁻¹ * (r * v) * g = (g⁻¹ * r * g) * (g⁻¹ * v * g) by group]
    exact mul_mem hrV hvV
  have hrv1 : r * v ≠ 1 := fun h => hr1 (by
    have hrv : r = v⁻¹ := eq_inv_of_mul_eq_one_left h
    rw [inv_eq_of_mul_eq_one_right C.v_mul_self] at hrv
    exact C.eq_one_of_mem_V_of_mem_Z hS D hr (hrv ▸ C.v_mem_Z hS))
  have hJ := D.mul_mem_longInv r hr v (C.v_mem_Z hS) hr1 C.v_ne_one
  have hconj : IsConj v (r * v) :=
    (C.isConj_of_mem_V hS D hxv hrvV (conj_ne_one hrv1)).trans
      (isConj_iff.mpr ⟨g, by group⟩)
  exact C.not_mem_longInv_of_isConj hconj hJ

theorem V_le_fixingSubgroup_x (hS : Sec4Setting G Ω) (D : C.Splitting hS) {T : Subgroup G}
    (hT : fusionIsSylowIn 2 T
      (Subgroup.centralizer ((Subgroup.zpowers v : Subgroup G) : Set G)))
    (hUT : D.U ⊔ C.Y ≤ T) (hxv : IsConj v C.x) :
    D.V ≤ fixingSubgroup G (fixSet Ω (Subgroup.zpowers C.x)) := fun r hr =>
  (mem_fixingSubgroup_iff G).mpr fun ω hω => by
    rcases eq_or_ne r 1 with rfl | hr1
    · exact one_smul G ω
    · rw [← C.fixSet_eq_of_mem_V hS D hT hUT hxv hr hr1, fixSet_zpowers, mem_fixedBy] at hω
      exact hω

theorem card_V_le_card_Z (hS : Sec4Setting G Ω) (D : C.Splitting hS) {T : Subgroup G}
    (hT : fusionIsSylowIn 2 T
      (Subgroup.centralizer ((Subgroup.zpowers v : Subgroup G) : Set G)))
    (hUT : D.U ⊔ C.Y ≤ T) (hxv : IsConj v C.x) : Nat.card D.V ≤ Nat.card C.Z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g₀, hg₀⟩ := isConj_iff.mp hxv
  set Φ := fixSet Ω (Subgroup.zpowers v)
  set A := D.V.map (MulAut.conj g₀⁻¹).toMonoidHom
  have hA2 : IsPGroup 2 A := (D.sylow.2.1.to_le D.V_le).map _
  have hVx := C.V_le_fixingSubgroup_x hS D hT hUT hxv
  have hFx : fixSet Ω (Subgroup.zpowers C.x) = g₀ • Φ := by rw [← hg₀, fixSet_zpowers_conj]
  have hAP : A ≤ fixingSubgroup G Φ := by
    rintro _ ⟨r, hr, rfl⟩
    refine (mem_fixingSubgroup_iff G).mpr fun ω hω => ?_
    have h1 : g₀ • ω ∈ fixSet Ω (Subgroup.zpowers C.x) := by
      rw [hFx]
      exact Set.smul_mem_smul_set hω
    have h2 := (mem_fixingSubgroup_iff G).mp (hVx hr) _ h1
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    rw [mul_smul, mul_smul, h2, inv_smul_smul]
  have hZ2 : IsPGroup 2 C.Z := C.sylow.2.1.to_le (C.Z_le_Y.trans C.Y_le_S)
  obtain ⟨P₂, hZP₂, hP₂⟩ := exists_fusionIsSylowIn_ge hZ2 (C.Z_le_fixingSubgroup hS)
  obtain ⟨T₀, hAT₀, hT₀⟩ := exists_fusionIsSylowIn_ge hA2 hAP
  obtain ⟨k, -, hk⟩ := exists_mem_conj_of_fusionIsSylowIn hP₂ hT₀
  have hmem : ∀ r : D.V, k⁻¹ * (g₀⁻¹ * (r : G) * g₀) * k ∈ C.Z := by
    intro r
    rcases eq_or_ne (r : G) 1 with h1 | h1
    · rw [h1, mul_one, inv_mul_cancel, mul_one, inv_mul_cancel]
      exact one_mem _
    · refine C.mem_Z_of_isConj_of_mem hS hP₂.2.1 hP₂.1 hZP₂ ?_ ((hk _).mp (hAT₀ ⟨r, r.2, ?_⟩))
      · exact (C.isConj_of_mem_V hS D hxv r.2 h1).trans
          (isConj_iff.mpr ⟨k⁻¹ * g₀⁻¹, by group⟩)
      · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
  refine Nat.card_le_card_of_injective (fun r : D.V => (⟨_, hmem r⟩ : C.Z)) fun r₁ r₂ h => ?_
  have h1 := congrArg Subtype.val h
  simp only at h1
  apply Subtype.ext
  calc (r₁ : G) = g₀ * (k * (k⁻¹ * (g₀⁻¹ * (r₁ : G) * g₀) * k) * k⁻¹) * g₀⁻¹ := by group
    _ = g₀ * (k * (k⁻¹ * (g₀⁻¹ * (r₂ : G) * g₀) * k) * k⁻¹) * g₀⁻¹ := by rw [h1]
    _ = r₂ := by group

theorem card_V_eq (hS : Sec4Setting G Ω) (D : C.Splitting hS) :
    Nat.card D.V = Nat.card (rootCenter (seRadical (C.Dv.M C.i)
      (C.Dv.coord ⟨C.γ, C.γ_mem⟩ C.i))) := by
  have hM := C.isNaturalSE_Dv C.i
  set γi := C.Dv.coord ⟨C.γ, C.γ_mem⟩ C.i
  have hC : ∀ {u : G}, u ∈ D.U →
      u ∈ Subgroup.centralizer ((Subgroup.zpowers v : Subgroup G) : Set G) := fun hu =>
    C.centralizer_Y_le hS (D.Mc_le (D.U_le hu))
  have hmem : ∀ r : D.V, C.piM hS ⟨r, hC (D.V_le r.2)⟩ ∈ rootCenter (seRadical (C.Dv.M C.i) γi) :=
    fun r => by
      have hR := D.piM_U_mem r (D.V_le r.2)
      refine hM.mem_rootCenter_seRadical (seRadical_le hR) (apply_eq_of_mem_seRadical hR) ?_
      rw [← map_mul, show (⟨r, hC (D.V_le r.2)⟩ : Subgroup.centralizer
        ((Subgroup.zpowers v : Subgroup G) : Set G)) * ⟨r, hC (D.V_le r.2)⟩ = 1 from
          Subtype.ext ((D.mem_V_iff r (D.V_le r.2)).mp r.2), map_one]
  refine Nat.card_eq_of_bijective (fun r : D.V => ⟨_, hmem r⟩) ⟨fun r₁ r₂ h => ?_, fun m => ?_⟩
  · have h1 := congrArg Subtype.val h
    simp only at h1
    have hU : (r₁ : G)⁻¹ * r₂ ∈ D.U := mul_mem (inv_mem (D.V_le r₁.2)) (D.V_le r₂.2)
    have h2 := D.piM_eq_one _ hU (by
      rw [show (⟨(r₁ : G)⁻¹ * r₂, C.centralizer_Y_le hS (D.Mc_le (D.U_le hU))⟩ :
        Subgroup.centralizer ((Subgroup.zpowers v : Subgroup G) : Set G)) =
          (⟨r₁, hC (D.V_le r₁.2)⟩)⁻¹ * ⟨r₂, hC (D.V_le r₂.2)⟩ from rfl, map_mul, map_inv, h1,
        inv_mul_cancel])
    exact Subtype.ext (inv_mul_eq_one.mp h2)
  · obtain ⟨u, hu, hum⟩ := D.exists_piM_U m (CFSG.GH74.Uniqueness.Bender.rootCenter_le _ m.2)
    have hu2 : u * u = 1 := D.piM_eq_one (u * u) (mul_mem hu hu) (by
      rw [show (⟨u * u, C.centralizer_Y_le hS (D.Mc_le (D.U_le (mul_mem hu hu)))⟩ :
        Subgroup.centralizer ((Subgroup.zpowers v : Subgroup G) : Set G)) = ⟨u, hC hu⟩ * ⟨u, hC hu⟩
        from rfl, map_mul, show C.piM hS ⟨u, hC hu⟩ = m from hum]
      exact hM.mul_self_eq_one_of_mem_rootCenter m.2)
    exact ⟨⟨u, (D.mem_V_iff u hu).mpr hu2⟩, Subtype.ext hum⟩

omit [Finite G] [Fintype Ω] [DecidableEq Ω] [FaithfulSMul G Ω] in
include C in
theorem conj_mem_centralizer_v {g₀ : G} (hg₀ : g₀ * v * g₀⁻¹ = C.x) {y : G}
    (hy : C.x * y = y * C.x) :
    g₀⁻¹ * y * g₀ ∈ Subgroup.centralizer ((Subgroup.zpowers v : Subgroup G) : Set G) := by
  refine mem_centralizer_zpowers ?_
  show v * (g₀⁻¹ * y * g₀) = g₀⁻¹ * y * g₀ * v
  have hv : v = g₀⁻¹ * C.x * g₀ := by rw [← hg₀]; group
  rw [hv]
  calc g₀⁻¹ * C.x * g₀ * (g₀⁻¹ * y * g₀) = g₀⁻¹ * (C.x * y) * g₀ := by group
    _ = g₀⁻¹ * (y * C.x) * g₀ := by rw [hy]
    _ = g₀⁻¹ * y * g₀ * (g₀⁻¹ * C.x * g₀) := by group

theorem inv_smul_γ_mem (hS : Sec4Setting G Ω) {g₀ : G} (hg₀ : g₀ * v * g₀⁻¹ = C.x) :
    g₀⁻¹ • (C.γ : Ω) ∈ fixSet Ω (Subgroup.zpowers v) := by
  have h1 : (C.γ : Ω) ∈ fixSet Ω (Subgroup.zpowers C.x) := by
    rw [fixSet_zpowers, mem_fixedBy]
    exact (C.x_smul hS).2.2
  rw [← hg₀, fixSet_zpowers_conj] at h1
  exact Set.mem_smul_set_iff_inv_smul_mem.mp h1

theorem eq_inv_smul_γ_of_mem_Z (hS : Sec4Setting G Ω) {g₀ : G} (hg₀ : g₀ * v * g₀⁻¹ = C.x)
    {z : G} (hz : z ∈ C.Z) (hz1 : z ≠ 1) {δ : Ω} (hδΦ : δ ∈ fixSet Ω (Subgroup.zpowers v))
    (hδ : (g₀⁻¹ * z * g₀) • δ = δ) : δ = g₀⁻¹ • (C.γ : Ω) := by
  have h1 : z • (g₀ • δ) = g₀ • δ := by
    rw [mul_smul, mul_smul, inv_smul_eq_iff] at hδ
    exact hδ
  have h2 : g₀ • δ ∈ fixSet Ω (Subgroup.zpowers v) := by
    rw [← C.fixSet_eq_of_mem_Z hS hz hz1, fixSet_zpowers, mem_fixedBy]
    exact h1
  have h3 : g₀ • δ ∈ fixSet Ω (Subgroup.zpowers C.x) := by
    rw [← hg₀, fixSet_zpowers_conj]
    exact Set.smul_mem_smul_set hδΦ
  rw [fixSet_zpowers, mem_fixedBy] at h3
  rw [← C.eq_γ_of_mem_fixSet_of_x_smul hS h2 h3, inv_smul_smul]

theorem piM_conj_Z_mem (hS : Sec4Setting G Ω) {g₀ : G} (hg₀ : g₀ * v * g₀⁻¹ = C.x) {z : G}
    (hz : z ∈ C.Z) :
    C.piM hS ⟨_, C.conj_mem_centralizer_v hg₀ (C.commute_x hS (C.Z_le_Y hz))⟩ ∈
      rootCenter (seRadical (C.Dv.M C.i) (C.Dv.coord ⟨_, C.inv_smul_γ_mem hS hg₀⟩ C.i)) := by
  have hM := C.isNaturalSE_Dv C.i
  set zC : Subgroup.centralizer ((Subgroup.zpowers v : Subgroup G) : Set G) :=
    ⟨_, C.conj_mem_centralizer_v hg₀ (C.commute_x hS (C.Z_le_Y hz))⟩
  rcases eq_or_ne z 1 with rfl | h1
  · rw [(C.piM_eq_one_iff hS zC).mpr fun ω _ => by
      show (g₀⁻¹ * 1 * g₀) • ω = ω
      rw [mul_one, inv_mul_cancel, one_smul]]
    exact one_mem _
  have hz2 : C.piM hS zC * C.piM hS zC = 1 := by
    rw [← map_mul, show zC * zC = 1 from Subtype.ext (by
      show g₀⁻¹ * z * g₀ * (g₀⁻¹ * z * g₀) = 1
      rw [show g₀⁻¹ * z * g₀ * (g₀⁻¹ * z * g₀) = g₀⁻¹ * (z * z) * g₀ by group,
        C.mul_self_eq_one_of_mem_Z hS hz, mul_one, inv_mul_cancel]), map_one]
  have hzc : C.piM hS zC (C.Dv.coord ⟨_, C.inv_smul_γ_mem hS hg₀⟩ C.i) =
      C.Dv.coord ⟨_, C.inv_smul_γ_mem hS hg₀⟩ C.i := by
    refine (C.smul_eq_iff_piM_apply_eq hS zC ⟨_, C.inv_smul_γ_mem hS hg₀⟩).mp ?_
    show (g₀⁻¹ * z * g₀) • g₀⁻¹ • (C.γ : Ω) = g₀⁻¹ • (C.γ : Ω)
    rw [mul_smul, mul_smul, smul_inv_smul, C.smul_eq_of_mem_Z_of_mem_fixSet hS hz C.γ_mem]
  have huniq : ∃! d, C.piM hS zC d = d := by
    refine ⟨_, hzc, fun d hd => ?_⟩
    obtain ⟨ω, rfl⟩ := C.Dv.exists_coord_apply_eq C.i d
    have hω := (C.smul_eq_iff_piM_apply_eq hS zC ω).mpr hd
    exact congrArg (fun p => C.Dv.coord p C.i)
      (Subtype.ext (C.eq_inv_smul_γ_of_mem_Z hS hg₀ hz h1 ω.2 hω))
  exact hM.mem_rootCenter_seRadical
    (hM.mem_of_existsUnique_fixed (C.piM_mem_normalizer hS zC) hz2 huniq) hzc hz2

theorem piM_conj_Z_injective (hS : Sec4Setting G Ω) {g₀ : G} (hg₀ : g₀ * v * g₀⁻¹ = C.x)
    {z₁ z₂ : G} (h₁ : z₁ ∈ C.Z) (h₂ : z₂ ∈ C.Z)
    (h : C.piM hS ⟨_, C.conj_mem_centralizer_v hg₀ (C.commute_x hS (C.Z_le_Y h₁))⟩ =
      C.piM hS ⟨_, C.conj_mem_centralizer_v hg₀ (C.commute_x hS (C.Z_le_Y h₂))⟩) :
    z₁ = z₂ := by
  have hz := mul_mem (inv_mem h₁) h₂
  have h2 : C.piM hS ⟨_, C.conj_mem_centralizer_v hg₀ (C.commute_x hS (C.Z_le_Y hz))⟩ = 1 := by
    rw [show (⟨_, C.conj_mem_centralizer_v hg₀ (C.commute_x hS (C.Z_le_Y hz))⟩ :
      Subgroup.centralizer ((Subgroup.zpowers v : Subgroup G) : Set G)) =
        (⟨_, C.conj_mem_centralizer_v hg₀ (C.commute_x hS (C.Z_le_Y h₁))⟩)⁻¹ *
          ⟨_, C.conj_mem_centralizer_v hg₀ (C.commute_x hS (C.Z_le_Y h₂))⟩ from Subtype.ext (by
        show g₀⁻¹ * (z₁⁻¹ * z₂) * g₀ = (g₀⁻¹ * z₁ * g₀)⁻¹ * (g₀⁻¹ * z₂ * g₀)
        group), map_mul, map_inv, h, inv_mul_cancel]
  have h3 := (C.piM_eq_one_iff hS _).mp h2
  by_contra hne
  have hne' : z₁⁻¹ * z₂ ≠ 1 := fun h => hne (inv_mul_eq_one.mp h)
  have hα := C.eq_inv_smul_γ_of_mem_Z hS hg₀ hz hne' C.isTypeL.mem_fixSet
    (h3 α C.isTypeL.mem_fixSet)
  have hβ := C.eq_inv_smul_γ_of_mem_Z hS hg₀ hz hne' C.mem_fixSet (h3 β C.mem_fixSet)
  exact C.ne (hα.trans hβ.symm)

theorem card_Z_le_card_V (hS : Sec4Setting G Ω) (D : C.Splitting hS) (hxv : IsConj v C.x) :
    Nat.card C.Z ≤ Nat.card D.V := by
  obtain ⟨n, i, e, hA⟩ := (C.isNaturalSE_Dv C.i).exists_isBenderAction
  obtain ⟨g₀, hg₀⟩ := isConj_iff.mp hxv
  have hle : Nat.card C.Z ≤ Nat.card (rootCenter (seRadical (C.Dv.M C.i)
      (C.Dv.coord ⟨_, C.inv_smul_γ_mem hS hg₀⟩ C.i))) :=
    Nat.card_le_card_of_injective (fun z : C.Z => (⟨_, C.piM_conj_Z_mem hS hg₀ z.2⟩ :
      rootCenter (seRadical (C.Dv.M C.i) (C.Dv.coord ⟨_, C.inv_smul_γ_mem hS hg₀⟩ C.i))))
      fun z₁ z₂ h => Subtype.ext (C.piM_conj_Z_injective hS hg₀ z₁.2 z₂.2
        (congrArg Subtype.val h))
  rw [C.card_V_eq hS D, hA.card_rootCenter_seRadical]
  rwa [hA.card_rootCenter_seRadical] at hle

theorem card_V_eq_card_Z (hS : Sec4Setting G Ω) (D : C.Splitting hS) {T : Subgroup G}
    (hT : fusionIsSylowIn 2 T
      (Subgroup.centralizer ((Subgroup.zpowers v : Subgroup G) : Set G)))
    (hUT : D.U ⊔ C.Y ≤ T) (hxv : IsConj v C.x) : Nat.card D.V = Nat.card C.Z :=
  le_antisymm (C.card_V_le_card_Z hS D hT hUT hxv) (C.card_Z_le_card_V hS D hxv)

end Theorem52

end FinConfig

end CFSG.Holt.H78
