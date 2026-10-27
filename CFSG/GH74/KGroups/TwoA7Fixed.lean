module

public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.ClassicalInvolution.SmallCases.Hat2A7Cover
public import CFSG.GH74.GLS.Pattern

public section

namespace CFSG.GH74.KGroups.TwoA7

open CFSG CFSG.ClassicalInvolution.Hat2A7 Equiv Equiv.Perm Subgroup CFSG.GH74.GLS

section Fixed

variable {E : Type} [Group E] {π : E →* A7} {z : E}

@[expose] def pi' (π : E →* A7) : E →* Perm (Fin 7) := (alternatingGroup (Fin 7)).subtype.comp π

theorem pi'_apply (π : E →* A7) (x : E) : pi' π x = (π x : Perm (Fin 7)) := rfl

@[expose] def centA (σ : Perm (Fin 7)) : Subgroup (Perm (Fin 7)) :=
  centralizer ({σ} : Set (Perm (Fin 7))) ⊓ alternatingGroup (Fin 7)

theorem mem_centA {σ y : Perm (Fin 7)} :
    y ∈ centA σ ↔ y * σ = σ * y ∧ y ∈ alternatingGroup (Fin 7) := by
  unfold centA
  rw [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]

theorem fixed_mem_cent (h : IsDoubleCoverA7 π z) (φ : MulAut E) {x : E}
    (hx : x ∈ fixedSubgroup E φ) : pi' π x ∈ centA (h.autPerm φ) := by
  rw [mem_centA]
  refine ⟨?_, (π x).2⟩
  have h1 := h.autPerm_spec φ x
  have h2 : φ x = x := hx
  rw [h2] at h1
  rw [pi'_apply]
  calc (π x : Perm (Fin 7)) * h.autPerm φ
      = (h.autPerm φ * (π x : Perm (Fin 7)) * (h.autPerm φ)⁻¹) * h.autPerm φ := by rw [← h1]
    _ = h.autPerm φ * (π x : Perm (Fin 7)) := by group

theorem sq_mem_fixed (h : IsDoubleCoverA7 π z) (φ : MulAut E) {x : E}
    (hx : pi' π x ∈ centralizer ({h.autPerm φ} : Set (Perm (Fin 7)))) :
    x * x ∈ fixedSubgroup E φ := by
  have hc : (π x : Perm (Fin 7)) * h.autPerm φ = h.autPerm φ * (π x : Perm (Fin 7)) :=
    Subgroup.mem_centralizer_singleton_iff.1 hx
  have hπ : π (φ x) = π x := by
    apply Subtype.ext
    rw [h.autPerm_spec φ x]
    calc h.autPerm φ * (π x : Perm (Fin 7)) * (h.autPerm φ)⁻¹
        = ((π x : Perm (Fin 7)) * h.autPerm φ) * (h.autPerm φ)⁻¹ := by rw [hc]
      _ = π x := by group
  have ht : π (x⁻¹ * φ x) = 1 := by rw [map_mul, map_inv, hπ, inv_mul_cancel]
  show φ (x * x) = x * x
  rw [map_mul]
  rcases (h.ker_iff _).1 ht with h1 | h1
  · have : φ x = x := by
      have h2 : x⁻¹ * φ x = 1 := h1
      exact (inv_mul_eq_one.1 h2).symm
    rw [this]
  · have h2 : φ x = x * z := by
      have h3 : x⁻¹ * φ x = z := h1
      calc φ x = x * (x⁻¹ * φ x) := by group
        _ = x * z := by rw [h3]
    rw [h2]
    calc (x * z) * (x * z) = x * (z * x) * z := by group
      _ = x * (x * z) * z := by rw [← h.central x]
      _ = x * x * (z * z) := by group
      _ = x * x := by rw [h.sq_eq_one, mul_one]

@[expose] noncomputable def rhoX (h : IsDoubleCoverA7 π z) (φ : MulAut E) {n : ℕ}
    (e : ↥(centA (h.autPerm φ)) ≃* Perm (Fin n)) : ↥(fixedSubgroup E φ) →* Perm (Fin n) :=
  e.toMonoidHom.comp (((pi' π).comp (fixedSubgroup E φ).subtype).codRestrict (centA (h.autPerm φ))
    (fun x => fixed_mem_cent h φ x.2))

theorem rhoX_apply (h : IsDoubleCoverA7 π z) (φ : MulAut E) {n : ℕ}
    (e : ↥(centA (h.autPerm φ)) ≃* Perm (Fin n)) (x : ↥(fixedSubgroup E φ)) :
    rhoX h φ e x = e ⟨pi' π (x : E), fixed_mem_cent h φ x.2⟩ := rfl

theorem rhoX_eq_one_iff (h : IsDoubleCoverA7 π z) (φ : MulAut E) {n : ℕ}
    (e : ↥(centA (h.autPerm φ)) ≃* Perm (Fin n)) (x : ↥(fixedSubgroup E φ)) :
    rhoX h φ e x = 1 ↔ (x : E) = 1 ∨ (x : E) = z := by
  rw [rhoX_apply, MulEquiv.map_eq_one_iff, ← (h.ker_iff (x : E))]
  constructor
  · intro h1
    have := congrArg Subtype.val h1
    exact Subtype.ext (by simpa [pi'_apply] using this)
  · intro h1
    apply Subtype.ext
    simp only [pi'_apply, OneMemClass.coe_one]
    rw [h1]
    rfl

theorem z_mem_fixed (h : IsDoubleCoverA7 π z) (φ : MulAut E) : z ∈ fixedSubgroup E φ := by
  show φ z = z
  have hz : (h.indAut φ) (π z) = π (φ z) := (h.indAut_spec φ z).symm
  rcases (h.ker_iff (φ z)).1 (by
    rw [h.indAut_spec φ z, (h.ker_iff z).2 (Or.inr rfl), map_one]) with h1 | h1
  · exfalso
    exact h.ne_one (φ.injective (by rw [h1, map_one]))
  · exact h1

theorem alternatingGroup_le_range_rhoX (h : IsDoubleCoverA7 π z) (φ : MulAut E) {n : ℕ}
    (e : ↥(centA (h.autPerm φ)) ≃* Perm (Fin n)) :
    alternatingGroup (Fin n) ≤ (rhoX h φ e).range := by
  have hsq : ∀ s : Perm (Fin n), s * s ∈ (rhoX h φ e).range := by
    intro s
    obtain ⟨hyc, hyA⟩ := mem_centA.1 (e.symm s).2
    obtain ⟨x, hx⟩ := h.surjective ⟨((e.symm s : ↥(centA (h.autPerm φ))) : Perm (Fin 7)), hyA⟩
    have hxc : pi' π x ∈ centralizer ({h.autPerm φ} : Set (Perm (Fin 7))) := by
      rw [Subgroup.mem_centralizer_singleton_iff, pi'_apply, hx]
      exact hyc
    refine ⟨⟨x * x, sq_mem_fixed h φ hxc⟩, ?_⟩
    rw [rhoX_apply]
    apply e.symm.injective
    rw [MulEquiv.symm_apply_apply]
    apply Subtype.ext
    have h1 : e.symm (s * s) = e.symm s * e.symm s := map_mul e.symm s s
    rw [h1]
    show pi' π (x * x) = ((e.symm s : ↥(centA (h.autPerm φ))) : Perm (Fin 7)) *
      ((e.symm s : ↥(centA (h.autPerm φ))) : Perm (Fin 7))
    rw [map_mul, pi'_apply, hx]
  rw [← Equiv.Perm.closure_three_cycles_eq_alternating]
  refine (Subgroup.closure_le _).2 (fun c hc => ?_)
  have h3 : c * (c * c) = 1 := by
    have := Equiv.Perm.IsThreeCycle.orderOf hc
    rw [← pow_three, ← this]
    exact pow_orderOf_eq_one c
  have h4 : c = (c * c) * (c * c) := by
    calc c = c * (c * (c * c)) := by rw [h3, mul_one]
      _ = (c * c) * (c * c) := by simp only [mul_assoc]
  rw [SetLike.mem_coe, h4]
  exact hsq (c * c)

end Fixed

section Quasi

open scoped commutatorElement

theorem isQuasisimple_of_cover {G S : Type*} [Group G] [Group S] [IsSimpleGroup S]
    (hSnc : ∃ a b : S, a * b ≠ b * a) (hSev : ∃ s : S, s * s = 1 ∧ s ≠ 1)
    (θ : G →* S) (hθ : Function.Surjective θ) {z : G}
    (hzc : ∀ g, g * z = z * g) (hker : ∀ w, θ w = 1 ↔ w = 1 ∨ w = z)
    (huniq : ∀ w : G, w * w = 1 → w = 1 ∨ w = z) : CFSG.IsQuasisimple G := by
  have hSperf : commutator S = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator S) with h0 | h0
    · exfalso
      obtain ⟨a, b, hab⟩ := hSnc
      apply hab
      have h1 : ⁅a, b⁆ ∈ commutator S :=
        Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
      rw [h0, Subgroup.mem_bot, commutatorElement_def] at h1
      calc a * b = a * b * a⁻¹ * b⁻¹ * b * a := by group
        _ = b * a := by rw [h1]; group
    · exact h0
  have hSZ : Subgroup.center S = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center S) with h0 | h0
    · exact h0
    · exfalso
      obtain ⟨a, b, hab⟩ := hSnc
      exact hab ((Subgroup.mem_center_iff.1 (by rw [h0]; exact Subgroup.mem_top b)) a)
  have hmap : (commutator G).map θ = ⊤ := by
    rw [map_commutator_eq G θ, MonoidHom.range_eq_top.mpr hθ]
    exact hSperf
  have hzD : z ∈ commutator G := by
    by_contra hzD
    obtain ⟨s, hs2, hs1⟩ := hSev
    have hs : s ∈ (commutator G).map θ := by rw [hmap]; exact Subgroup.mem_top s
    obtain ⟨d, hd, hds⟩ := hs
    have hdsq : d * d = 1 := by
      have h1 : θ (d * d) = 1 := by rw [map_mul, hds]; exact hs2
      rcases (hker _).1 h1 with h2 | h2
      · exact h2
      · exact absurd (h2 ▸ Subgroup.mul_mem _ hd hd) hzD
    rcases huniq d hdsq with h2 | h2
    · exact hs1 (by rw [← hds, h2, map_one])
    · exact hzD (h2 ▸ hd)
  have hGperf : commutator G = ⊤ := by
    rw [eq_top_iff]
    intro g _
    have hg : θ g ∈ (commutator G).map θ := by rw [hmap]; exact Subgroup.mem_top _
    obtain ⟨d, hd, hdg⟩ := hg
    have h1 : θ (d⁻¹ * g) = 1 := by rw [map_mul, map_inv, hdg, inv_mul_cancel]
    have h2 : d⁻¹ * g ∈ commutator G := by
      rcases (hker _).1 h1 with h3 | h3
      · rw [h3]; exact Subgroup.one_mem _
      · rw [h3]; exact hzD
    have : g = d * (d⁻¹ * g) := by group
    rw [this]
    exact Subgroup.mul_mem _ hd h2
  have hcenter : Subgroup.center G = θ.ker := by
    apply le_antisymm
    · intro g hg
      have h1 : θ g ∈ Subgroup.center S := Subgroup.map_center_le_center hθ ⟨g, hg, rfl⟩
      rw [hSZ] at h1
      exact h1
    · intro g hg
      rw [MonoidHom.mem_ker, hker] at hg
      rw [Subgroup.mem_center_iff]
      intro k
      rcases hg with rfl | rfl
      · simp
      · exact hzc k
  let eC : (G ⧸ Subgroup.center G) ≃* S :=
    (QuotientGroup.quotientMulEquivOfEq hcenter).trans
      (QuotientGroup.quotientKerEquivOfSurjective θ hθ)
  refine ⟨Group.isPerfect_def.mpr hGperf, (MulEquiv.isSimpleGroup_congr eC).mpr inferInstance, ?_⟩
  obtain ⟨a, b, hab⟩ := hSnc
  exact ⟨eC.symm a, eC.symm b, fun h1 => hab (by simpa using congrArg eC h1)⟩

theorem isPComponent_of_normal {X : Type*} [Group X] (hX : pPrimeCore 2 X = ⊥) {L : Subgroup X}
    [L.Normal] (hL : CFSG.IsQuasisimple L) : IsPComponent 2 L := by
  have hinj : Function.Injective (QuotientGroup.mk' (pPrimeCore 2 X)) := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', hX]
  refine ⟨L.map (QuotientGroup.mk' (pPrimeCore 2 X)), ⟨?_, ?_⟩,
    Subgroup.Normal.isSubnormal ‹_›, rfl, ?_⟩
  · exact CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.equivMapOfInjective L _ hinj) hL
  · exact (Subgroup.Normal.map ‹L.Normal› _ (QuotientGroup.mk'_surjective _)).isSubnormal
  · intro J hJ _ hmap
    have hJL : J = L := by
      apply le_antisymm hJ.le
      intro x hx
      have h1 : (QuotientGroup.mk' (pPrimeCore 2 X)) x ∈
          J.map (QuotientGroup.mk' (pPrimeCore 2 X)) := by
        rw [hmap]; exact ⟨x, hx, rfl⟩
      obtain ⟨y, hy, hxy⟩ := h1
      exact (hinj hxy) ▸ hy
    exact absurd hJL (ne_of_lt hJ)

end Quasi

end CFSG.GH74.KGroups.TwoA7
