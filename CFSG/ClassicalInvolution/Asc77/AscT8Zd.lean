module

public import CFSG.ClassicalInvolution.Asc77.AscT8Four

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.Thompson
  CFSG.GH74.Uniqueness CFSG.StronglyEmbedded.UniqueCoset

namespace T8

section PD

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem isProductDisconnected_of_centralizer {H : Subgroup G} (hH : H ≠ ⊤) {z : G}
    (h1 : ∃! c : G ⧸ H, z • c = c)
    (hc : ∀ u ∈ productInvolutions (conjugatesOf z), u ∈ H →
      Subgroup.centralizer ({u} : Set G) ≤ H) :
    IsProductDisconnected (conjugatesOf z) H := by
  refine ⟨hH, ?_, fun x hx hxH g => ?_, hc⟩
  · obtain ⟨c, hc', -⟩ := h1
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective c
    exact ⟨g⁻¹ * z * g, isConj_iff.2 ⟨g⁻¹, by group⟩, (smul_coe_eq_iff H z g).1 hc'⟩
  · have hu := existsUnique_fixed_of_isConj hx h1
    have h1x : x • ((1 : G) : G ⧸ H) = ((1 : G) : G ⧸ H) :=
      (smul_coe_eq_iff H x 1).2 (by simpa using hxH)
    constructor
    · intro hg
      have hgx : x • (g : G ⧸ H) = g := (smul_coe_eq_iff H x g).2 hg
      have h := QuotientGroup.eq.1 (hu.unique hgx h1x)
      simpa using h
    · intro hg
      exact H.mul_mem (H.mul_mem (H.inv_mem hg) hxH) hg

theorem false_of_centralizer_clause {H : Subgroup G} {z : G} (hH : H ≠ ⊤) (hz : orderOf z = 2)
    (h1 : ∃! c : G ⧸ H, z • c = c)
    (hc : ∀ u ∈ productInvolutions (conjugatesOf z), u ∈ H →
      Subgroup.centralizer ({u} : Set G) ≤ H)
    {F : Subgroup G} [F.Normal] (hFs : IsSimpleGroup ↥F)
    (hFnab : ∃ x ∈ F, ∃ y ∈ F, x * y ≠ y * x) (hFc : Subgroup.centralizer (F : Set G) = ⊥)
    {K : Subgroup G} (hK : K ≤ Subgroup.centralizer ({z} : Set G))
    (hKs : ¬ Group.IsSolvable ↥K) : False := by
  have hsolv : Group.IsSolvable ↥(Subgroup.centralizer ({z} : Set G)) :=
    isSolvable_centralizer_of_ZDConclusion hz h1 hFs hFnab hFc rfl
      (S_ZD_unconditional G (conjugatesOf z) H (isInvariantInvolutionSet hz)
        (isProductDisconnected_of_centralizer hH h1 hc))
  exact hKs (Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hK)
    (Subgroup.inclusion_injective hK))

end PD

section Reduce

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}

theorem centralizer_le_H274_of_isConj {K J : Subgroup G} {S : Sylow 2 G} {R T W : Subgroup G}
    {z t : G} (hs : Std8 p f Ω K J S R T W z t) (hcomp : dComp Ω K = dstarComp Ω K) {u : G}
    (hu : IsConj z u) (huH : u ∈ H274 Ω K z) : Subgroup.centralizer ({u} : Set G) ≤ H274 Ω K z := by
  obtain ⟨v, rfl⟩ := isConj_iff.1 hu
  have hvH : v⁻¹ ∈ H274 Ω K z := mem_H274_of_conj_mem_H274 hs hcomp (by simpa using huH)
  have hv : v ∈ H274 Ω K z := by simpa using (H274 Ω K z).inv_mem hvH
  have hCz : Subgroup.centralizer ({z} : Set G) ≤ H274 Ω K z :=
    (centralizer_le_normalizer_of_noTwins hs.stand.hyp.conjInvariant hs.stand.mem hs.noTwins
      hs.hz).trans
      ((normalizer_le_sigmaNorm hs.stand.hyp.conjInvariant hs.stand.mem).trans
        (sigmaNorm_le_H274 K z))
  intro c hc
  rw [Subgroup.mem_centralizer_singleton_iff] at hc
  have hc' : v⁻¹ * c * v ∈ Subgroup.centralizer ({z} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc v⁻¹ * c * v * z = v⁻¹ * (c * (v * z * v⁻¹)) * v := by group
      _ = v⁻¹ * ((v * z * v⁻¹) * c) * v := by rw [hc]
      _ = z * (v⁻¹ * c * v) := by group
  have h := (H274 Ω K z).mul_mem ((H274 Ω K z).mul_mem hv (hCz hc')) hvH
  simpa [mul_assoc] using h

end Reduce

end T8

variable (p f : ℕ) [Fact p.Prime]

@[expose] def C27_4b : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G)) (K J : Subgroup G)
    (S : Sylow 2 G) (R T W : Subgroup G) (z t : G), Std8 p f Ω K J S R T W z t →
      ¬ DConnected Ω → ∀ g : G, g⁻¹ * (z * t) * g ∈ T8.H274 Ω K z →
        Subgroup.centralizer ({g⁻¹ * (z * t) * g} : Set G) ≤ T8.H274 Ω K z

variable {p f}

theorem c27_4b_of_c27_4a (h : C27_4a p f) : C27_4b p f := by
  intro G _ _ _ Ω K J S R T W z t hs hdisc g hg c hc
  have hfix : (z * t) • ((g : G) : G ⧸ T8.H274 Ω K z) = (g : G ⧸ T8.H274 Ω K z) :=
    (smul_coe_eq_iff _ _ g).2 hg
  have hAH : z * t ∈ T8.H274 Ω K z :=
    T8.centralizer_mul_le_H274 hs.hJ hs.ht (Subgroup.mem_centralizer_singleton_iff.mpr rfl)
  have hfix1 : (z * t) • (((1 : G)) : G ⧸ T8.H274 Ω K z) = ((1 : G) : G ⧸ T8.H274 Ω K z) :=
    (smul_coe_eq_iff _ _ 1).2 (by simpa using hAH)
  have hgH : g ∈ T8.H274 Ω K z := by
    have := (h G Ω K J S R T W z t hs hdisc).unique hfix hfix1
    have h2 := QuotientGroup.eq.1 this
    simpa using h2
  rw [Subgroup.mem_centralizer_singleton_iff] at hc
  have hcg : g * c * g⁻¹ ∈ Subgroup.centralizer ({z * t} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc g * c * g⁻¹ * (z * t) = g * (c * (g⁻¹ * (z * t) * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * (z * t) * g) * c) * g⁻¹ := by rw [hc]
      _ = (z * t) * (g * c * g⁻¹) := by group
  have h3 := T8.centralizer_mul_le_H274 (z := z) hs.hJ hs.ht hcg
  have h4 := (T8.H274 Ω K z).mul_mem ((T8.H274 Ω K z).mul_mem ((T8.H274 Ω K z).inv_mem hgH) h3) hgH
  simpa [mul_assoc] using h4

theorem c27_4_of_steps_b (h2 : C27_2 p f) (h4b : C27_4b p f) : C27_4 p f := by
  intro G _ _ _ Ω K J S R T W z t hs hdisc
  have hcomp : dComp Ω K = dstarComp Ω K := h2 G Ω K J S R T W z t hs hdisc
  by_contra hne
  have hH : T8.H274 Ω K z ≠ ⊤ := hne
  have hz := hs.hz
  have hz2 : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact hz.sq) hz.ne_one
  have h1 : ∃! c : G ⧸ T8.H274 Ω K z, z • c = c := T8.fixesUniqueCoset_z hs hcomp
  have hc : ∀ u ∈ productInvolutions (conjugatesOf z), u ∈ T8.H274 Ω K z →
      Subgroup.centralizer ({u} : Set G) ≤ T8.H274 Ω K z := by
    rintro u ⟨hu2, x, hx, y, hy, hxy, rfl⟩ huH
    obtain ⟨c, rfl⟩ := isConj_iff.1 hx
    obtain ⟨c', rfl⟩ := isConj_iff.1 hy
    obtain ⟨e, he⟩ : ∃ e, e = c⁻¹ * c' := ⟨_, rfl⟩
    have hy0 : c⁻¹ * (c' * z * c'⁻¹) * c = e * z * e⁻¹ := by
      rw [he]
      group
    have hcomm0 : z * (e * z * e⁻¹) = e * z * e⁻¹ * z := by
      rw [← hy0]
      calc z * (c⁻¹ * (c' * z * c'⁻¹) * c)
          = c⁻¹ * ((c * z * c⁻¹) * (c' * z * c'⁻¹)) * c := by group
        _ = c⁻¹ * ((c' * z * c'⁻¹) * (c * z * c⁻¹)) * c := by rw [hxy]
        _ = c⁻¹ * (c' * z * c'⁻¹) * c * z := by group
    have hu0 : c * z * c⁻¹ * (c' * z * c'⁻¹) = c * (z * (e * z * e⁻¹)) * c⁻¹ := by
      rw [he]
      group
    have hne0 : e * z * e⁻¹ ≠ z := by
      intro h
      rw [h] at hu0
      have : c * z * c⁻¹ * (c' * z * c'⁻¹) = 1 := by rw [hu0, hz.sq]; group
      rw [this, orderOf_one] at hu2
      omega
    have hne0' : (e⁻¹)⁻¹ * z * e⁻¹ ≠ z := by simpa using hne0
    have hcomm0' : z * ((e⁻¹)⁻¹ * z * e⁻¹) = (e⁻¹)⁻¹ * z * e⁻¹ * z := by simpa using hcomm0
    rcases T8.isConj_or_mem_omegaNbr hs.stand hs.noTwins hz hne0' hcomm0' with hconj | hnbr
    · have hconj' : IsConj z (z * (e * z * e⁻¹)) := by simpa using hconj
      have hconjx : IsConj z (c * z * c⁻¹ * (c' * z * c'⁻¹)) := by
        rw [hu0]
        exact hconj'.trans (isConj_iff.2 ⟨c, rfl⟩)
      exact T8.centralizer_le_H274_of_isConj hs hcomp hconjx huH
    · have hM : conjSub e K ∈ omegaNbr Ω K := by simpa using hnbr
      have hM2 : IsUniqueInvolution (conjSub e K) (e * z * e⁻¹) := hz.conj e
      obtain ⟨S', R', T', W', hstd⟩ := c27_setup_proved G Ω K hs.stand hs.noTwins hdisc z hz
        (conjSub e K) hM (e * z * e⁻¹) hM2
      have hg : (c⁻¹)⁻¹ * (z * (e * z * e⁻¹)) * c⁻¹ ∈ T8.H274 Ω K z := by
        rw [inv_inv, ← hu0]
        exact huH
      have := h4b G Ω K (conjSub e K) S' R' T' W' z (e * z * e⁻¹) hstd hdisc c⁻¹ hg
      rwa [inv_inv, ← hu0] at this
  have hKs := CFSG.StronglyEmbedded.UniqueCoset.not_isSolvable_of_mem hs.stand.hyp hs.stand.mem hz
  have hnab : ∃ a b : G, a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    have : Group.IsSolvable G := IsSimpleGroup.comm_iff_isSolvable.mp hcon
    exact hKs inferInstance
  have hTs : IsSimpleGroup ↥(⊤ : Subgroup G) :=
    (Subgroup.topEquiv : ↥(⊤ : Subgroup G) ≃* G).isSimpleGroup
  have hTnab : ∃ x ∈ (⊤ : Subgroup G), ∃ y ∈ (⊤ : Subgroup G), x * y ≠ y * x := by
    obtain ⟨a, b, h⟩ := hnab
    exact ⟨a, Subgroup.mem_top a, b, Subgroup.mem_top b, h⟩
  have hTc : Subgroup.centralizer ((⊤ : Subgroup G) : Set G) = ⊥ := by
    rw [Subgroup.coe_top, Subgroup.centralizer_univ]
    rcases Subgroup.Normal.eq_bot_or_eq_top (Subgroup.center G) with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnab
      have hb : b ∈ Subgroup.center G := by rw [h]; exact Subgroup.mem_top b
      exact hab (Subgroup.mem_center_iff.1 hb a)
  exact T8.false_of_centralizer_clause hH hz2 h1 hc hTs hTnab hTc
    (CFSG.StronglyEmbedded.UniqueCoset.le_centralizer_of_isUniqueInvolution hz) hKs

end CFSG.ClassicalInvolution.Asc77
